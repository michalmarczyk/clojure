;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

; Author: Frantisek Sodomka, Mike Hinchey, Stuart Halloway

;;
;;  Test "flow control" constructs.
;;

(ns clojure.test-clojure.control
  (:use clojure.test
        clojure.test-helper)
  (:import (clojure.lang Compiler$CompilerException)))

;; *** Helper functions ***

(defn maintains-identity [f]
  (are [x] (= (f x) x)
      nil
      false true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      () '(1 2)
      [] [1 2]
      {} {:a 1 :b 2}
      #{} #{1 2} ))


; http://clojure.org/special_forms
; http://clojure.org/macros

(deftest test-do
  (are [x y] (= x y)
      ; no params => nil
      (do) nil
      
      ; return last
      (do 1) 1
      (do 1 2) 2
      (do 1 2 3 4 5) 5
      
      ; evaluate and return last
      (let [a (atom 0)]
        (do (reset! a (+ @a 1))   ; 1
            (reset! a (+ @a 1))   ; 2
            (reset! a (+ @a 1))   ; 3
            @a))  3 )

  ; identity (= (do x) x)
  (maintains-identity (fn [_] (do _))) )


;; loop/recur
(deftest test-loop
  (are [x y] (= x y)
       nil (loop [])
       1 (loop []
           1)
       3 (loop [a 1]
           (if (< a 3)
             (recur (inc a))
             a))
       [2 4 6] (loop [a []
                      b [1 2 3]]
                 (if (seq b)
                   (recur (conj a (* 2 (first b)))
                          (next b))
                   a))
       [6 4 2] (loop [a ()
                      b [1 2 3]]
                 (if (seq b)
                   (recur (conj a (* 2 (first b)))
                          (next b))
                   a))
       )
  (is (thrown? Compiler$CompilerException
               (eval '(loop []
                        (recur)
                        :recur-not-in-tail-position))))
  (is (thrown? Compiler$CompilerException
               (eval '(loop []
                        (try
                          (recur)
                          (catch Throwable _)))))))

(deftest test-named-loop
  (are [x y] (= x y)
       nil (loop nil [])
       nil (loop foo [])
       9 (loop foo [x 3 a 0]
           (if (zero? x)
             a
             (loop [y 3 b 0]
               (if (zero? y)
                 (recur-to foo (dec x) (+ a b))
                 (recur (dec y) (inc b))))))
       378 (let [m [[[1 2 3] [4 5 6] [7 8 9]]
                    [[10 11 12] [13 14 15] [16 17 18]]
                    [[19 20 21] [22 23 24] [25 26 27]]]]
             (loop iloop [i 0 ires 0]
               (if (== i (count m))
                 ires
                 (loop jloop [j 0 jres 0]
                   (if (== j (count (get m i)))
                     (recur-to iloop (inc i) (+ ires jres))
                     (loop [k 0 kres 0]
                       (if (== k (count (get-in m [i j])))
                         (recur-to jloop (inc j) (+ jres kres))
                         (recur (inc k) (+ kres (get-in m [i j k]))))))))))
       10 (loop foo [x 0]
            (if (pos? x)
              x
              (loop bar [x 3]
                (if-not (== x 3)
                  (throw (Exception.)))
                (loop bar [y 5]
                  (if (< y 7)
                    (recur-to bar (inc y))
                    (recur-to foo (+ x y))))))))
  (is (thrown? Compiler$CompilerException
               (eval '(loop foo []
                        (loop []
                          (recur-to foo)
                          :recur-to-not-in-tail-position)))))
  (is (thrown? Compiler$CompilerException
               (eval '(loop foo []
                        (loop bar []
                          (loop []
                            (recur-to unknown-loop-label)))))))
  (is (thrown? Compiler$CompilerException
               (eval '(loop recur-across-try []
                        (try
                          (recur-to recur-across-try)
                          (catch Throwable _)))))))


;; fn/recur

(deftest test-fn-recur
  (are [x y] (= x y)
    3 ((fn [a]
         (if (< a 3)
           (recur (inc a))
           a))
        1)
    [2 4 6] ((fn [a b]
               (if (seq b)
                 (recur (conj a (* 2 (first b)))
                        (next b))
                 a))
              []
              [1 2 3])
    [6 4 2] ((fn [a b]
               (if (seq b)
                 (recur (conj a (* 2 (first b)))
                        (next b))
                 a))
              ()
              [1 2 3])
    )
  (is (thrown? Compiler$CompilerException
               (eval '(fn []
                        (recur)
                        :recur-not-in-tail-position)))))

(deftest test-named-fn-recur-to
  (are [x y] (= x y)
    9 ((fn foo [x a]
         (if (zero? x)
           a
           (loop [y 3 b 0]
             (if (zero? y)
               (recur-to foo (dec x) (+ a b))
               (recur (dec y) (inc b))))))
        3
        0)
    378 (let [m [[[1 2 3] [4 5 6] [7 8 9]]
                 [[10 11 12] [13 14 15] [16 17 18]]
                 [[19 20 21] [22 23 24] [25 26 27]]]]
          ((fn iloop [i ires]
             (if (== i (count m))
               ires
               (loop jloop [j 0 jres 0]
                 (if (== j (count (get m i)))
                   (recur-to iloop (inc i) (+ ires jres))
                   (loop [k 0 kres 0]
                     (if (== k (count (get-in m [i j])))
                       (recur-to jloop (inc j) (+ jres kres))
                       (recur (inc k) (+ kres (get-in m [i j k])))))))))
            0
            0))
    10 ((fn foo [x]
          (if (pos? x)
            x
            (loop bar [x 3]
              (if-not (== x 3)
                (throw (Exception.)))
              (loop bar [y 5]
                (if (< y 7)
                  (recur-to bar (inc y))
                  (recur-to foo (+ x y)))))))
         0))
  (is (thrown? Compiler$CompilerException
               (eval '(fn foo []
                        (loop []
                          (recur-to foo)
                          :recur-to-not-in-tail-position)))))
  (is (thrown? Compiler$CompilerException
               (eval '(fn foo []
                        (loop bar []
                          (loop []
                            (recur-to unknown-loop-label))))))))


;; defn/recur-to

(defn test-foo-1
  ([x a]
   (if (zero? x)
     a
     (loop [y 3 b 0]
       (if (zero? y)
         (recur-to test-foo-1 (dec x) (+ a b))
         (recur (dec y) (inc b))))))
  ([x y a]
   (if (zero? x)
     a
     (loop [z y b 0]
       (if (zero? z)
         (recur-to test-foo-1 (dec x) (dec y) (+ a b))
         (recur (dec z) (inc b)))))))

(let [m [[[1 2 3] [4 5 6] [7 8 9]]
         [[10 11 12] [13 14 15] [16 17 18]]
         [[19 20 21] [22 23 24] [25 26 27]]]]

  (defn test-foo-2 [i ires]
    (if (== i (count m))
      ires
      (loop jloop [j 0 jres 0]
        (if (== j (count (get m i)))
          (recur-to test-foo-2 (inc i) (+ ires jres))
          (loop [k 0 kres 0]
            (if (== k (count (get-in m [i j])))
              (recur-to jloop (inc j) (+ jres kres))
              (recur (inc k) (+ kres (get-in m [i j k]))))))))))

(defn test-foo-3 [x]
  (if (pos? x)
    x
    (loop bar [x 3]
      (if-not (== x 3)
        (throw (Exception.)))
      (loop bar [y 5]
        (if (< y 7)
          (recur-to bar (inc y))
          (recur-to test-foo-3 (+ x y)))))))

(deftest test-defn-recur-to
  (are [x y] (= x y)
    9 (test-foo-1 3 0)
    12 (test-foo-1 3 5 0)
    378 (test-foo-2 0 0)
    10 (test-foo-3 0))
  (is (thrown? Compiler$CompilerException
               (eval '(defn test-foo-4 []
                        (loop []
                          (recur-to test-foo-4)
                          :recur-to-not-in-tail-position)))))
  (is (thrown? Compiler$CompilerException
               (eval '(defn test-foo-5 []
                        (loop bar []
                          (loop []
                            (recur-to unknown-loop-label))))))))


;; throw, try

; if: see logic.clj

(deftest test-when
  (are [x y] (= x y)
       1 (when true 1)
       nil (when true)
       nil (when false)
       nil (when false (exception))
       ))

(deftest test-when-not
  (are [x y] (= x y)
       1 (when-not false 1)
       nil (when-not true)
       nil (when-not false)
       nil (when-not true (exception))
       ))

(deftest test-if-not
  (are [x y] (= x y)
       1 (if-not false 1)
       1 (if-not false 1 (exception))
       nil (if-not true 1)
       2 (if-not true 1 2)
       nil (if-not true (exception))
       1 (if-not true (exception) 1)
       ))

(deftest test-when-let
  (are [x y] (= x y)
       1 (when-let [a 1]
           a)
       2 (when-let [[a b] '(1 2)]
           b)
       nil (when-let [a false]
             (exception))
       ))

(deftest test-if-let
  (are [x y] (= x y)
       1 (if-let [a 1]
           a)
       2 (if-let [[a b] '(1 2)]
           b)
       nil (if-let [a false]
             (exception))
       1 (if-let [a false]
           a 1)
       1 (if-let [[a b] nil]
             b 1)
       1 (if-let [a false]
           (exception)
           1)
       ))

(deftest test-when-first
  (are [x y] (= x y)
       1 (when-first [a [1 2]]
           a)
       2 (when-first [[a b] '((1 2) 3)]
           b)
       nil (when-first [a nil]
             (exception))
       ))

(deftest test-if-some
  (are [x y] (= x y)
       1 (if-some [a 1] a)
       false (if-some [a false] a)
       nil (if-some [a nil] (exception))
       3 (if-some [[a b] [1 2]] (+ a b))
       1 (if-some [[a b] nil] b 1)
       1 (if-some [a nil] (exception) 1)))

(deftest test-when-some
  (are [x y] (= x y)
       1 (when-some [a 1] a)
       2 (when-some [[a b] [1 2]] b)
       false (when-some [a false] a)
       nil (when-some [a nil] (exception))))

(deftest test-cond
  (are [x y] (= x y)
      (cond) nil

      (cond nil true) nil
      (cond false true) nil
      
      (cond true 1 true (exception)) 1
      (cond nil 1 false 2 true 3 true 4) 3
      (cond nil 1 false 2 true 3 true (exception)) 3 )

  ; false
  (are [x]  (= (cond x :a true :b) :b)
      nil false )

  ; true
  (are [x]  (= (cond x :a true :b) :a)
      true
      0 42
      0.0 3.14
      2/3
      0M 1M
      \c
      "" "abc"
      'sym
      :kw
      () '(1 2)
      [] [1 2]
      {} {:a 1 :b 2}
      #{} #{1 2} )

  ; evaluation
  (are [x y] (= x y)
      (cond (> 3 2) (+ 1 2) true :result true (exception)) 3
      (cond (< 3 2) (+ 1 2) true :result true (exception)) :result )

  ; identity (= (cond true x) x)
  (maintains-identity (fn [_] (cond true _))) )


(deftest test-condp
  (are [x] (= :pass x)
       (condp = 1
         1 :pass
         2 :fail)
       (condp = 1
         2 :fail
         1 :pass)
       (condp = 1
         2 :fail
         :pass)
       (condp = 1
         :pass)
       (condp = 1
         2 :fail
         ;; doc of condp says result-expr is returned
         ;; shouldn't it say similar to cond: "evaluates and returns
         ;; the value of the corresponding expr and doesn't evaluate any of the
         ;; other tests or exprs."
         (identity :pass))
       (condp + 1
         1 :>> #(if (= % 2) :pass :fail))
       (condp + 1
         1 :>> #(if (= % 3) :fail :pass))
       )
  (is (thrown? IllegalArgumentException
               (condp = 1)
               ))
  (is (thrown? IllegalArgumentException
               (condp = 1
                 2 :fail)
               ))
  )


; [for, doseq (for.clj)]

(deftest test-dotimes
  ;; dotimes always returns nil
  (is (= nil (dotimes [n 1] n)))
  ;; test using an atom since dotimes is for modifying
  ;; test executes n times
  (is (= 3
         (let [a (atom 0)]
           (dotimes [n 3]
             (swap! a inc))
           @a)
         ))
  ;; test all values of n
  (is (= [0 1 2]
         (let [a (atom [])]
           (dotimes [n 3]
             (swap! a conj n))
           @a)))
  (is (= []
         (let [a (atom [])]
           (dotimes [n 0]
             (swap! a conj n))
           @a)))
  )

(deftest test-while
  (is (= nil (while nil (throw (Exception. "never")))))
  (is (= [0 nil]
         ;; a will dec to 0
         ;; while always returns nil
         (let [a (atom 3)
               w (while (pos? @a)
                   (swap! a dec))]
           [@a w])))
  (is (thrown? Exception (while true (throw (Exception. "expected to throw")))))
  )

; locking, monitor-enter, monitor-exit

; case 
(deftest test-case
  (testing "can match many kinds of things"
    (let [two 2
          test-fn
          #(case %
                 1 :number
                 "foo" :string
                 \a :char
                 pow :symbol
                 :zap :keyword
                 (2 \b "bar") :one-of-many
                 [1 2] :sequential-thing
                 {:a 2} :map
                 {:r 2 :d 2} :droid
                 #{2 3 4 5} :set
                 [1 [[[2]]]] :deeply-nested
                 nil :nil
                 :default)]
      (are [result input] (= result (test-fn input))
           :number 1
           :string "foo"
           :char \a
           :keyword :zap
           :symbol 'pow
           :one-of-many 2
           :one-of-many \b
           :one-of-many "bar"
           :sequential-thing [1 2]
           :sequential-thing (list 1 2)
           :sequential-thing [1 two]
           :map {:a 2}
           :map {:a two}
           :set #{2 3 4 5}
           :set #{two 3 4 5}
           :default #{2 3 4 5 6}
           :droid {:r 2 :d 2}
           :deeply-nested [1 [[[two]]]]
           :nil nil
           :default :anything-not-appearing-above)))
  (testing "throws IllegalArgumentException if no match"
    (is (thrown-with-msg?
          IllegalArgumentException #"No matching clause: 2"
          (case 2 1 :ok))))
  (testing "sorting doesn't matter"
    (let [test-fn
          #(case %
                {:b 2 :a 1} :map
                #{3 2 1} :set
                :default)]
      (are [result input] (= result (test-fn input))
           :map {:a 1 :b 2}
           :map (sorted-map :a 1 :b 2)
           :set #{3 2 1}
           :set (sorted-set 2 1 3))))
  (testing "test number equivalence"
    (is (= :1 (case 1N 1 :1 :else))))
  (testing "test warn when boxing/hashing expr for all-ints case"
    (should-print-err-message
      #"Performance warning, .*:\d+ - case has int tests, but tested expression is not primitive..*\r?\n"
      (let [x (Object.)] (case x 1 1 2))))
  (testing "test correct behavior on sparse ints"
    (are [result input] (= result (case input
                                    2r1000000000000000000000000000000 :big
                                    1 :small
                                    :else))
         :small 1
         :big 1073741824
         :else 2)
    (are [result input] (= result (case input
                                    1 :small
                                    2r1000000000000000000000000000000 :big
                                    :else))
         :small 1
         :big 1073741824
         :else 2))
  (testing "test emits return types"
    (should-not-reflect (Long. (case 1 1 1))) ; new Long(long)
    (should-not-reflect (Long. (case 1 1 "1")))) ; new Long(String)
  (testing "short or byte expr compiles and matches"
    (is (= 3 (case (short 4) 1 2 3)))
    (is (= 3 (case (byte 4) 1 2 3))))
  (testing "non-equivalence of chars and nums"
    (are [result input] (= result (case input 97 :97 :else))
      :else \a
      :else (char \a)
      :97 (int \a))
    (are [result input] (= result (case input \a :a :else))
      :else 97
      :else 97N
      :a (char 97)))
  (testing "test error on duplicate test constants"
    (is (thrown-with-cause-msg?
          clojure.lang.Compiler$CompilerException
          #"Duplicate case test constant: 1"
          (eval `(case 0 1 :x 1 :y)))))
  (testing "test correct behaviour on Number truncation"
    (let [^Object x (Long. 8589934591)  ; force bindings to not be emitted as a primitive long
          ^Object y (Long. -1)]
      (is (= :diff (case x -1 :oops :diff)))
      (is (= :same (case y -1 :same :oops)))))
  (testing "test correct behavior on hash collision"
    ;; case uses Java .hashCode to put values into hash buckets.
    (is (== (.hashCode 1) (.hashCode 9223372039002259457N)))
    (are [result input] (= result (case input
                                    1 :long
                                    9223372039002259457N :big
                                    :else))
         :long 1
         :big 9223372039002259457N
         :else 4294967296
         :else 2)
    (are [result input] (= result (case input
                                    9223372039002259457N :big
                                    1 :long
                                    :else))
         :long 1
         :big 9223372039002259457N
         :else 4294967296
         :else 2)
    (are [result input] (= result (case input
                                    0 :zero
                                    -1 :neg1
                                    2 :two
                                    :oops :OOPS))
         :zero 0
         :neg1 -1
         :two 2
         :OOPS :oops)
    (are [result input] (= result (case input
                                    1204766517646190306 :a
                                    1 :b
                                    -2 :c
                                    :d))
         :a 1204766517646190306
         :b 1
         :c -2
         :d 4294967296
         :d 3))
  (testing "test warn for hash collision"
    (should-print-err-message
     #"Performance warning, .*:\d+ - hash collision of some case test constants; if selected, those entries will be tested sequentially..*\r?\n"
     (case 1 1 :long 9223372039002259457N :big 2)))
  (testing "test constants are *not* evaluated"
    (let [test-fn
          ;; never write code like this...
          #(case %
                 (throw (RuntimeException. "boom")) :piece-of-throw-expr
                 :no-match)]
      (are [result input] (= result (test-fn input))
           :piece-of-throw-expr 'throw
           :piece-of-throw-expr '[RuntimeException. "boom"]
           :no-match nil))))
