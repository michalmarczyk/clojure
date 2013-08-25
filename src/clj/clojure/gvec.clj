;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

;;; a generic vector implementation for vectors of primitives

(in-ns 'clojure.core)

(import '(clojure.lang Murmur3))

(defmacro ^:private caching-hash [coll hash-fn hash-key]
  `(let [h# ~hash-key]
     (if-not (== h# (int -1))
       h#
       (let [h# (~hash-fn ~coll)]
         (set! ~hash-key (int h#))
         h#))))

(defn ^:private hash-gvec [^clojure.lang.IPersistentVector v]
  (let [cnt (.count v)]
    (loop [h (int 1) i (int 0)]
      (if (== i cnt)
        h
        (let [v (.nth v i)]
          (recur (unchecked-add-int (unchecked-multiply-int 31 h)
                                    (clojure.lang.Util/hash v))
                 (unchecked-inc i)))))))

(defn ^:private hash-gvec-seq [xs]
  (let [cnt (count xs)]
    (loop [h (int 1) xs (seq xs)]
      (if xs
        (let [x (first xs)]
          (recur (unchecked-add-int (unchecked-multiply-int 31 h)
                                    (clojure.lang.Util/hash x))
                 (next xs)))
        h))))

(def ^:private ^:const empty-vector-hashcode (.hashCode []))
(def ^:private ^:const empty-vector-hasheq   (hash []))

;(set! *warn-on-reflection* true)

(deftype VecNode [^java.util.concurrent.atomic.AtomicReference edit arr])

(def EMPTY-NODE (VecNode. nil (object-array 32)))

(definterface IVecImpl
  (^int tailoff [])
  (arrayFor [^int i])
  (pushTail [^int level ^clojure.core.VecNode parent ^clojure.core.VecNode tailnode])
  (popTail [^int level node])
  (newPath [edit ^int level node])
  (doAssoc [^int level node ^int i val]))

(definterface ArrayManager
  (array [^int size])
  (^int alength [arr])
  (aclone [arr])
  (aget [arr ^int i])
  (aset [arr ^int i val]))

(deftype ArrayChunk [^clojure.core.ArrayManager am arr ^int off ^int end]
  
  clojure.lang.Indexed
  (nth [_ i] (.aget am arr (+ off i)))
  
  (count [_] (- end off))

  clojure.lang.IChunk
  (dropFirst [_]
    (if (= off end)
      (throw (IllegalStateException. "dropFirst of empty chunk"))
      (new ArrayChunk am arr (inc off) end)))
  
  (reduce [_ f init]
    (loop [ret init i off]
      (if (< i end)
        (recur (f ret (.aget am arr i)) (inc i))
        ret)))
  )

(deftype VecSeq [^clojure.core.ArrayManager am ^clojure.core.IVecImpl vec anode ^int i ^int offset
                 ^:unsynchronized-mutable ^int _hash
                 ^:unsynchronized-mutable ^int _hasheq]
  :no-print true

  clojure.core.protocols.InternalReduce
  (internal-reduce
   [_ f val]
   (loop [result val
          aidx offset]
     (if (< aidx (count vec))
       (let [node (.arrayFor vec aidx)
             result (loop [result result
                           node-idx (bit-and 0x1f aidx)]
                      (if (< node-idx (.alength am node))
                        (recur (f result (.aget am node node-idx)) (inc node-idx))
                        result))]
         (recur result (bit-and 0xffe0 (+ aidx 32))))
       result)))

  Object
  (toString [this]
    (pr-str this))

  (hashCode [this]
    (caching-hash this hash-gvec-seq _hash))

  (equals [this that]
    (cond
      (identical? this that) true
      (not (or (sequential? that) (instance? java.util.List that))) false
      :else
      (loop [xs this ys (seq that)]
        (if xs
          (if ys
            (if (clojure.lang.Util/equals (first xs) (first ys))
              (recur (next xs) (next ys))
              false)
            false)
          (nil? ys)))))

  clojure.lang.IHashEq
  (hasheq [this]
    (caching-hash this Murmur3/hashOrdered _hasheq))
  
  clojure.lang.ISeq
  (first [_] (.aget am anode offset))
  (next [this] 
    (if (< (inc offset) (.alength am anode))
      (new VecSeq am vec anode i (inc offset) -1 -1)
      (.chunkedNext this)))
  (more [this]
    (let [s (.next this)]
      (or s (clojure.lang.PersistentList/EMPTY))))
  (cons [this o]
    (clojure.lang.Cons. o this))
  (count [this]
    (loop [i 1
           s (next this)]
      (if s
        (if (instance? clojure.lang.Counted s)
          (+ i (.count s))
          (recur (inc i) (next s)))
        i)))
  (equiv [this o]
    (cond
     (identical? this o) true
     (or (instance? clojure.lang.Sequential o) (instance? java.util.List o))
     (loop [me this
            you (seq o)]
       (if (nil? me)
         (nil? you)
         (and (clojure.lang.Util/equiv (first me) (first you))
              (recur (next me) (next you)))))
     :else false))
  (empty [_]
    clojure.lang.PersistentList/EMPTY)


  clojure.lang.Seqable
  (seq [this] this)

  clojure.lang.IChunkedSeq
  (chunkedFirst [_] (ArrayChunk. am anode offset (.alength am anode)))
  (chunkedNext [_] 
   (let [nexti (+ i (.alength am anode))]
     (when (< nexti (count vec))
       (new VecSeq am vec (.arrayFor vec nexti) nexti 0 -1 -1))))
  (chunkedMore [this]
    (let [s (.chunkedNext this)]
      (or s (clojure.lang.PersistentList/EMPTY)))))

(defmethod print-method ::VecSeq [v w]
  ((get (methods print-method) clojure.lang.ISeq) v w))

(declare ->TVec)

(defn- editable-root [^clojure.core.VecNode root]
  (VecNode. (java.util.concurrent.atomic.AtomicReference. (Thread/currentThread))
            (aclone ^objects (.-arr root))))

(defn- editable-tail [^clojure.core.ArrayManager am tail]
  (let [ret (.array am 32)]
    (System/arraycopy tail 0 ret 0 (.alength am tail))
    ret))

(deftype Vec [^clojure.core.ArrayManager am ^int cnt ^int shift ^clojure.core.VecNode root tail _meta
              ^:unsynchronized-mutable ^int _hash
              ^:unsynchronized-mutable ^int _hasheq]
  Object
  (equals [this o]
    (cond 
     (identical? this o) true
     (or (instance? clojure.lang.IPersistentVector o) (instance? java.util.RandomAccess o))
       (and (= cnt (count o))
            (loop [i (int 0)]
              (cond
               (= i cnt) true
               (.equals (.nth this i) (nth o i)) (recur (inc i))
               :else false)))
     (or (instance? clojure.lang.Sequential o) (instance? java.util.List o))
       (if-let [st (seq this)]
         (.equals st (seq o))
         (nil? (seq o)))
     :else false))

  (hashCode [this]
    (caching-hash this hash-gvec _hash))

  clojure.lang.IHashEq
  (hasheq [this]
    (caching-hash this Murmur3/hashOrdered _hasheq))

  clojure.lang.Counted
  (count [_] cnt)

  clojure.lang.IMeta
  (meta [_] _meta)

  clojure.lang.IObj
  (withMeta [_ m] (new Vec am cnt shift root tail m _hash _hasheq))

  clojure.lang.Indexed
  (nth [this i]
    (let [a (.arrayFor this i)]
      (.aget am a (bit-and i (int 0x1f)))))
  (nth [this i not-found]
       (let [z (int 0)]
         (if (and (>= i z) (< i (.count this)))
           (.nth this i)
           not-found)))

  clojure.lang.IPersistentCollection
  (cons [this val]
     (if (< (- cnt (.tailoff this)) (int 32))
      (let [new-tail (.array am (inc (.alength am tail)))]
        (System/arraycopy tail 0 new-tail 0 (.alength am tail))
        (.aset am new-tail (.alength am tail) val)
        (new Vec am (inc cnt) shift root new-tail (meta this) -1 -1))
      (let [tail-node (VecNode. (.edit root) tail)] 
        (if (> (bit-shift-right cnt (int 5)) (bit-shift-left (int 1) shift)) ;overflow root?
          (let [new-root (VecNode. (.edit root) (object-array 32))]
            (doto ^objects (.arr new-root)
              (aset 0 root)
              (aset 1 (.newPath this (.edit root) shift tail-node)))
            (new Vec am (inc cnt) (+ shift (int 5)) new-root (let [tl (.array am 1)] (.aset am  tl 0 val) tl) (meta this) -1 -1))
          (new Vec am (inc cnt) shift (.pushTail this shift root tail-node)
                 (let [tl (.array am 1)] (.aset am  tl 0 val) tl) (meta this) -1 -1)))))

  (empty [_] (new Vec am 0 5 EMPTY-NODE (.array am 0) nil empty-vector-hashcode empty-vector-hasheq))
  (equiv [this o]
    (cond 
     (or (instance? clojure.lang.IPersistentVector o) (instance? java.util.RandomAccess o))
       (and (= cnt (count o))
            (loop [i (int 0)]
              (cond
               (= i cnt) true
               (= (.nth this i) (nth o i)) (recur (inc i))
               :else false)))
     (or (instance? clojure.lang.Sequential o) (instance? java.util.List o))
       (clojure.lang.Util/equiv (seq this) (seq o))
     :else false))

  clojure.lang.IPersistentStack
  (peek [this]
    (when (> cnt (int 0)) 
      (.nth this (dec cnt))))

  (pop [this]
   (cond
    (zero? cnt) 
      (throw (IllegalStateException. "Can't pop empty vector"))
    (= 1 cnt) 
    (new Vec am 0 5 EMPTY-NODE (.array am 0) (meta this) empty-vector-hashcode empty-vector-hasheq)
    (> (- cnt (.tailoff this)) 1)
      (let [new-tail (.array am (dec (.alength am tail)))]
        (System/arraycopy tail 0 new-tail 0 (.alength am new-tail))
        (new Vec am (dec cnt) shift root new-tail (meta this) -1 -1))
    :else
      (let [new-tail (.arrayFor this (- cnt 2))
            new-root ^clojure.core.VecNode (.popTail this shift root)]
        (cond
         (nil? new-root) 
           (new Vec am (dec cnt) shift EMPTY-NODE new-tail (meta this) -1 -1)
         (and (> shift 5) (nil? (aget ^objects (.arr new-root) 1)))
           (new Vec am (dec cnt) (- shift 5) (aget ^objects (.arr new-root) 0) new-tail (meta this) -1 -1)
         :else
           (new Vec am (dec cnt) shift new-root new-tail (meta this) -1 -1)))))

  clojure.lang.IPersistentVector
  (assocN [this i val]
    (cond 
     (and (<= (int 0) i) (< i cnt))
       (if (>= i (.tailoff this))
         (let [new-tail (.array am (.alength am tail))]
           (System/arraycopy tail 0 new-tail 0 (.alength am tail))
           (.aset am new-tail (bit-and i (int 0x1f)) val)
           (new Vec am cnt shift root new-tail (meta this) -1 -1))
         (new Vec am cnt shift (.doAssoc this shift root i val) tail (meta this) -1 -1))
     (= i cnt) (.cons this val)
     :else (throw (IndexOutOfBoundsException.))))
  
  clojure.lang.Reversible
  (rseq [this]
        (if (> (.count this) 0)
          (clojure.lang.APersistentVector$RSeq. this (dec (.count this)))
          nil))
  
  clojure.lang.Associative
  (assoc [this k v]
    (if (clojure.lang.Util/isInteger k)
      (.assocN this k v)
      (throw (IllegalArgumentException. "Key must be integer"))))
  (containsKey [this k]
    (and (clojure.lang.Util/isInteger k)
         (<= 0 (int k))
         (< (int k) cnt)))
  (entryAt [this k]
    (if (.containsKey this k)
      (clojure.lang.MapEntry. k (.nth this (int k)))
      nil))

  clojure.lang.ILookup
  (valAt [this k not-found]
    (if (clojure.lang.Util/isInteger k)
      (let [i (int k)]
        (if (and (>= i 0) (< i cnt))
          (.nth this i)
          not-found))
      not-found))

  (valAt [this k] (.valAt this k nil))

  clojure.lang.IFn
  (invoke [this k]
    (if (clojure.lang.Util/isInteger k)
      (let [i (int k)]
        (if (and (>= i 0) (< i cnt))
          (.nth this i)
          (throw (IndexOutOfBoundsException.))))
      (throw (IllegalArgumentException. "Key must be integer"))))

  
  clojure.lang.Seqable
  (seq [this] 
    (if (zero? cnt) 
      nil
      (VecSeq. am this (.arrayFor this 0) 0 0 _hash _hasheq)))

  clojure.lang.Sequential ;marker, no methods

  clojure.core.IVecImpl
  (tailoff [_] 
    (- cnt (.alength am tail)))

  (arrayFor [this i]
    (if (and  (<= (int 0) i) (< i cnt))
      (if (>= i (.tailoff this))
        tail
        (loop [node root level shift]
          (if (zero? level)
            (.arr node)
            (recur (aget ^objects (.arr node) (bit-and (bit-shift-right i level) (int 0x1f))) 
                   (- level (int 5))))))
      (throw (IndexOutOfBoundsException.))))

  (pushTail [this level parent tailnode]
    (let [subidx (bit-and (bit-shift-right (dec cnt) level) (int 0x1f))
          parent ^clojure.core.VecNode parent
          ret (VecNode. (.edit parent) (aclone ^objects (.arr parent)))
          node-to-insert (if (= level (int 5))
                           tailnode
                           (let [child (aget ^objects (.arr parent) subidx)]
                             (if child
                               (.pushTail this (- level (int 5)) child tailnode)
                               (.newPath this (.edit root) (- level (int 5)) tailnode))))]
      (aset ^objects (.arr ret) subidx node-to-insert)
      ret))

  (popTail [this level node]
    (let [node ^clojure.core.VecNode node
          subidx (bit-and (bit-shift-right (- cnt (int 2)) level) (int 0x1f))]
      (cond
       (> level 5)
         (let [new-child (.popTail this (- level 5) (aget ^objects (.arr node) subidx))]
           (if (and (nil? new-child) (zero? subidx))
             nil
             (let [arr (aclone ^objects (.arr node))]
               (aset arr subidx new-child)
               (VecNode. (.edit root) arr))))
       (zero? subidx) nil
       :else (let [arr (aclone ^objects (.arr node))]
               (aset arr subidx nil)
               (VecNode. (.edit root) arr)))))

  (newPath [this edit ^int level node]
    (if (zero? level)
      node
      (let [ret (VecNode. edit (object-array 32))]
        (aset ^objects (.arr ret) 0 (.newPath this edit (- level (int 5)) node))
        ret)))

  (doAssoc [this level node i val]
    (let [node ^clojure.core.VecNode node]       
      (if (zero? level)
        ;on this branch, array will need val type
        (let [arr (.aclone am (.arr node))]
          (.aset am arr (bit-and i (int 0x1f)) val)
          (VecNode. (.edit node) arr))
        (let [arr (aclone ^objects (.arr node))
              subidx (bit-and (bit-shift-right i level) (int 0x1f))]
          (aset arr subidx (.doAssoc this (- level (int 5)) (aget arr subidx) i val))
          (VecNode. (.edit node) arr)))))

  clojure.lang.IEditableCollection
  (asTransient [this]
    (->TVec am cnt shift (editable-root root) (editable-tail am tail)))

  java.lang.Comparable
  (compareTo [this o]
    (if (identical? this o)
      0
      (let [^clojure.lang.IPersistentVector v (cast clojure.lang.IPersistentVector o)
            vcnt (.count v)]
        (cond
          (< cnt vcnt) -1
          (> cnt vcnt) 1
          :else
            (loop [i (int 0)]
              (if (= i cnt)
                0
                (let [comp (clojure.lang.Util/compare (.nth this i) (.nth v i))]
                  (if (= 0 comp)
                    (recur (inc i))
                    comp))))))))

  java.lang.Iterable
  (iterator [this]
    (let [i (java.util.concurrent.atomic.AtomicInteger. 0)]
      (reify java.util.Iterator
        (hasNext [_] (< (.get i) cnt))
        (next [_] (.nth this (dec (.incrementAndGet i))))
        (remove [_] (throw (UnsupportedOperationException.))))))

  java.util.Collection
  (contains [this o] (boolean (some #(= % o) this)))
  (containsAll [this c] (every? #(.contains this %) c))
  (isEmpty [_] (zero? cnt))
  (toArray [this] (into-array Object this))
  (toArray [this arr]
    (if (>= (count arr) cnt)
      (do
        (dotimes [i cnt]
          (aset arr i (.nth this i)))
        arr)
      (into-array Object this)))
  (size [_] cnt)
  (add [_ o] (throw (UnsupportedOperationException.)))
  (addAll [_ c] (throw (UnsupportedOperationException.)))
  (clear [_] (throw (UnsupportedOperationException.)))
  (^boolean remove [_ o] (throw (UnsupportedOperationException.)))
  (removeAll [_ c] (throw (UnsupportedOperationException.)))
  (retainAll [_ c] (throw (UnsupportedOperationException.)))

  java.util.List
  (get [this i] (.nth this i))
  (indexOf [this o]
    (loop [i (int 0)]
      (cond
        (== i cnt) -1
        (= o (.nth this i)) i
        :else (recur (inc i)))))
  (lastIndexOf [this o]
    (loop [i (dec cnt)]
      (cond
        (< i 0) -1
        (= o (.nth this i)) i
        :else (recur (dec i)))))
  (listIterator [this] (.listIterator this 0))
  (listIterator [this i]
    (let [i (java.util.concurrent.atomic.AtomicInteger. i)]
      (reify java.util.ListIterator
        (hasNext [_] (< (.get i) cnt))
        (hasPrevious [_] (pos? i))
        (next [_] (.nth this (dec (.incrementAndGet i))))
        (nextIndex [_] (.get i))
        (previous [_] (.nth this (.decrementAndGet i)))
        (previousIndex [_] (dec (.get i)))
        (add [_ e] (throw (UnsupportedOperationException.)))
        (remove [_] (throw (UnsupportedOperationException.)))
        (set [_ e] (throw (UnsupportedOperationException.))))))
  (subList [this a z] (subvec this a z))
  (add [_ i o] (throw (UnsupportedOperationException.)))
  (addAll [_ i c] (throw (UnsupportedOperationException.)))
  (^Object remove [_ ^int i] (throw (UnsupportedOperationException.)))
  (set [_ i e] (throw (UnsupportedOperationException.)))
)

(defmethod print-method ::Vec [v w]
  ((get (methods print-method) clojure.lang.IPersistentVector) v w))

(defmacro mk-am {:private true} [t]
  (let [garr (gensym)
        tgarr (with-meta garr {:tag (symbol (str t "s"))})]
    `(reify clojure.core.ArrayManager
            (array [_ size#] (~(symbol (str t "-array")) size#))
            (alength [_ ~garr] (alength ~tgarr))
            (aclone [_ ~garr] (aclone ~tgarr))
            (aget [_ ~garr i#] (aget ~tgarr i#))
            (aset [_ ~garr i# val#] (aset ~tgarr i# (~t val#))))))

(def ^{:private true} ams
     {:int (mk-am int)
      :long (mk-am long)
      :float (mk-am float)
      :double (mk-am double)
      :byte (mk-am byte)
      :short (mk-am short)
      :char (mk-am char)
      :boolean (mk-am boolean)})

(defn vector-of 
  "Creates a new vector of a single primitive type t, where t is one
  of :int :long :float :double :byte :short :char or :boolean. The
  resulting vector complies with the interface of vectors in general,
  but stores the values unboxed internally.

  Optionally takes one or more elements to populate the vector."
  {:added "1.2"
   :arglists '([t] [t & elements])}
  ([t]
   (let [am ^clojure.core.ArrayManager (ams t)]
     (Vec. am 0 5 EMPTY-NODE (.array am 0) nil
           empty-vector-hashcode empty-vector-hasheq)))
  ([t x1]
   (let [am ^clojure.core.ArrayManager (ams t)
         arr (.array am 1)]
     (.aset am arr 0 x1)
     (Vec. am 1 5 EMPTY-NODE arr nil -1 -1)))
  ([t x1 x2]
   (let [am ^clojure.core.ArrayManager (ams t)
         arr (.array am 2)]
     (.aset am arr 0 x1)
     (.aset am arr 1 x2)
     (Vec. am 2 5 EMPTY-NODE arr nil -1 -1)))
  ([t x1 x2 x3]
   (let [am ^clojure.core.ArrayManager (ams t)
         arr (.array am 3)]
     (.aset am arr 0 x1)
     (.aset am arr 1 x2)
     (.aset am arr 2 x3)
     (Vec. am 3 5 EMPTY-NODE arr nil -1 -1)))
  ([t x1 x2 x3 x4]
   (let [am ^clojure.core.ArrayManager (ams t)
         arr (.array am 4)]
     (.aset am arr 0 x1)
     (.aset am arr 1 x2)
     (.aset am arr 2 x3)
     (.aset am arr 3 x4)
     (Vec. am 4 5 EMPTY-NODE arr nil -1 -1)))
  ([t x1 x2 x3 x4 & xn]
   (loop [v  (transient (vector-of t x1 x2 x3 x4))
          xn xn]
     (if xn
       (recur (.conj ^clojure.lang.ITransientVector v (first xn)) (next xn))
       (persistent! v)))))

(definterface ITVecImpl
  (ensureEditable [])
  (^clojure.core.VecNode ensureEditable [^clojure.core.VecNode node ^int shift])
  (editableArrayFor [^int i]))

(deftype TVec [^clojure.core.ArrayManager am
               ^:unsynchronized-mutable ^int cnt
               ^:unsynchronized-mutable ^int shift
               ^:unsynchronized-mutable ^clojure.core.VecNode root
               ^:unsynchronized-mutable tail]
  clojure.lang.Counted
  (count [this]
    (.ensureEditable this)
    cnt)

  clojure.core.IVecImpl
  (tailoff [this]
    (if (< cnt 32)
      0
      (bit-shift-left (bit-shift-right (dec cnt) 5) 5)))

  (arrayFor [this i]
    (if (and  (<= (int 0) i) (< i cnt))
      (if (>= i (.tailoff this))
        tail
        (loop [node root level shift]
          (if (zero? level)
            (.arr node)
            (recur (aget ^objects (.arr node) (bit-and (bit-shift-right i level) (int 0x1f))) 
                   (- level (int 5))))))
      (throw (IndexOutOfBoundsException.))))

  (pushTail [this level parent tailnode]
    (let [parent (.ensureEditable this parent level)
          subidx (bit-and (bit-shift-right (dec cnt) level) 0x1f)
          node-to-insert (if (== level 5)
                           tailnode
                           (let [child (aget ^objects (.-arr parent) subidx)]
                             (if (nil? child)
                               (.newPath this (.-edit root) level tailnode)
                               (.pushTail this (- level 5) child tailnode))))]
      (aset ^objects (.-arr parent) subidx node-to-insert)
      parent))

  (newPath [this edit ^int level node]
    (if (zero? level)
      node
      (let [ret (VecNode. edit (object-array 32))]
        (aset ^objects (.arr ret) 0 (.newPath this edit (- level (int 5)) node))
        ret)))

  (doAssoc [this ^int level node ^int i val]
    (let [ret (.ensureEditable this node level)]
      (if (zero? level)
        (.aset am (.-arr ret) (bit-and i 0x1f) val)
        (let [subidx (bit-and (bit-shift-right 1 level) 0x1f)]
          (aset ^objects (.-arr ret) subidx
                (.doAssoc this (- level 5) (aget ^objects (.-arr ret) subidx) i val))))
      ret))

  (popTail [this level node]
    (let [node ^clojure.core.VecNode (.ensureEditable this node)
          subidx (bit-and (bit-shift-right (- cnt (int 2)) level) (int 0x1f))]
      (cond
       (> level 5)
         (let [new-child (.popTail this (- level 5) (aget ^objects (.arr node) subidx))]
           (if (and (nil? new-child) (zero? subidx))
             nil
             (let [arr (.-arr node)]
               (aset ^objects arr subidx new-child)
               node)))
       (zero? subidx) nil
       :else (let [arr (.-arr node)]
               (aset ^objects arr subidx nil)
               node))))

  clojure.core.ITVecImpl
  (ensureEditable [this]
    (let [owner (.. root -edit (get))]
      (if-not (identical? owner (Thread/currentThread))
        (if (nil? owner)
          (throw (IllegalAccessError. "Transient used after persistent! call"))
          (throw (IllegalAccessError. "Transient used by non-owner thread"))))))

  (ensureEditable [this node shift]
    (if (identical? (.-edit node) (.-edit root))
      node
      (if (zero? shift)
        (VecNode. (.-edit root) (.aclone am (.-arr node)))
        (VecNode. (.-edit root) (aclone ^objects (.-arr node))))))

  (editableArrayFor [this i]
    (if (and  (<= (int 0) i) (< i cnt))
      (if (>= i (.tailoff this))
        tail
        (loop [node root level shift]
          (if (zero? level)
            (.arr node)
            (recur (.ensureEditable this (aget ^objects (.arr node) (bit-and (bit-shift-right i level) (int 0x1f))) level)
                   (- level (int 5))))))
      (throw (IndexOutOfBoundsException.))))

  clojure.lang.ITransientVector
  (assocN [this i val]
    (.ensureEditable this)
    (if (and (>= i 0) (< i cnt))
      (if (>= i (.tailoff this))
        (do (.aset am tail (bit-and i 0x1f) val)
            this)
        (do (set! root (.doAssoc this shift root i val))
            this))
      (if (== i cnt)
        (.conj this val)
        (throw (IndexOutOfBoundsException.)))))

  (pop [this]
    (.ensureEditable this)
    (cond
      (zero? cnt)
      (throw (IllegalStateException. "Can't pop empty vector"))

      (== 1 cnt)
      (do (set! cnt (int 0))
          this)

      (> (- cnt (.tailoff this)) 1)
      (do (set! cnt (unchecked-dec-int cnt))
          this)

      :else
      (let [new-tail (.editableArrayFor this (- cnt 2))
            new-root ^clojure.core.VecNode (.popTail this shift root)]
        (set! cnt  (unchecked-dec-int cnt))
        (set! tail new-tail)
        (cond
          (nil? new-root)
          (do (set! root (VecNode. (.-edit root) (object-array 32)))
              this)

          (and (> shift 5) (nil? (aget ^objects (.arr new-root) 1)))
          (do (set! shift (unchecked-subtract-int shift (int 5)))
              (set! root  (.ensureEditable this (aget ^objects (.-arr new-root) 0) shift))
              this)

          :else
          (do (set! root new-root)
              this)))))

  clojure.lang.ITransientAssociative
  (assoc [this key val]
    (if (clojure.lang.Util/isInteger key)
      (let [i (int key)]
        (.assocN this i val))
      (IllegalArgumentException. "Key must be integer")))

  clojure.lang.ITransientCollection
  (conj [this val]
    (.ensureEditable this)
    (if (< (- cnt (.tailoff this)) (int 32))
      (do (.aset am tail (bit-and cnt (int 0x1f)) val)
          (set! cnt (unchecked-inc-int cnt))
          this)
      (let [tail-node (VecNode. (.-edit root) tail)
            new-tail  (.array am 32)]
        (.aset am new-tail 0 val)
        (set! tail new-tail)
        (if (> (bit-shift-right cnt (int 5))
               (bit-shift-left (int 1) shift))
          (let [new-root-array (object-array 32)
                new-shift      (unchecked-add-int shift (int 5))]
            (aset ^objects new-root-array 0 root)
            (aset ^objects new-root-array 1 (.newPath this (.-edit root) shift tail-node))
            (set! root  (VecNode. (.-edit root) new-root-array))
            (set! shift new-shift)
            (set! cnt   (unchecked-inc-int cnt))
            this)
          (let [new-root (.pushTail this shift root tail-node)]
            (set! root new-root)
            (set! cnt  (unchecked-inc-int cnt))
            this)))))

  (persistent [this]
    (.ensureEditable this)
    (.. root -edit (set nil))
    (let [trimmed-tail (.array am (- cnt (.tailoff this)))]
      (System/arraycopy tail 0 trimmed-tail 0 (.alength am trimmed-tail))
      (Vec. am cnt shift root trimmed-tail nil -1 -1)))

  clojure.lang.ILookup
  (valAt [this k] (.valAt this k nil))

  (valAt [this k not-found]
    (if (clojure.lang.Util/isInteger k)
      (let [i (int k)]
        (if (and (>= i 0) (< i cnt))
          (.nth this i)
          not-found))
      not-found))

  clojure.lang.Indexed
  (nth [this i]
    (let [a (.arrayFor this i)]
      (.aget am a (bit-and i (int 0x1f)))))

  (nth [this i not-found]
    (let [z (int 0)]
      (if (and (>= i z) (< i (.count this)))
        (.nth this i)
        not-found)))

  clojure.lang.IFn
  (invoke [this k]
    (if (clojure.lang.Util/isInteger k)
      (let [i (int k)]
        (if (and (>= i 0) (< i cnt))
          (.nth this i)
          (throw (IndexOutOfBoundsException.))))
      (throw (IllegalArgumentException. "Key must be integer"))))

  (applyTo [this args]
    (let [len (clojure.lang.RT/boundedLength args 20)]
      (if (== len 1)
        (.invoke this (first args))
        (throw (clojure.lang.ArityException. len "transient gvec"))))))
