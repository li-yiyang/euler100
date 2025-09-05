;;;; euler100.lisp --- Ryo's solution to the first 100 problems of Project Euler

;;; License:
;; this package is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License,
;; or (at your option) any later version.
;;
;; this package is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this package. If not, see <https://www.gnu.org/licenses/>.
;;

;;; Commentary:
;;

(defpackage #:euler
  (:use :cl))

(in-package :euler)


;;;; Utilies
;; You could skip these functions and macros, they are just used here
;; to make sure the code is neat and readable.
;;
;; However, if you are new to Common Lisp, this part can be a short
;; introduction of Common Lisp.
;;

;;; Constants:
;; In Common Lisp, you could use:
;; + `(defparameter name value [docstring])'
;; + `(defvar name [value] [docstring])'
;; to define global variables.
;;
;; The difference between `defparameter' and `defvar':
;; if variable is already defined, it's value will not be
;; rebind in `defvar' but would be updated in `defparameter'.
;;
;; Use `(defconstant name value [docstring])' can
;; define global constant.
;;

(defconstant +thousand+ 1000    "One thousand. ")
(defconstant +million+  1000000 "One Million. ")

;;; Types:
;; These types are more mathematically used
;;
;; Types could be declared in functions like:
;; + (declare (type TYPE VAR...))
;;
;;   normally, the type of variable could be determined by compiler.
;;   or you could manually declare it, for example:
;;   + (or function symbol) either function or symbol
;;   + (member :key1 :key2) one of :key1, :key2
;;   + (satisfies testf)    ensures element pass testf
;;
;; + (the TYPE EXPR)
;;
;;   normally, the return value of EXPR could be determined by compiler.
;;   or you could manually declare it with `the' form.
;;

(deftype natural (&optional (low 1) (high '*))
  "Natural number starting from LOW, LOW + 1, ..., HIGH"
  `(integer ,low ,high))

(deftype positive-integer ()
  "Integers that is positive. "
  '(integer 1))

;;; Tools defining new functions and macros
;; + `with-gensym' is a `let' like functionality
;;
;;   the utility function `gensym' is used to avoid name conflicts
;;   for example:
;;
;;       `(let ((x 1)) (lambda (,arg) (+ ,arg x)))
;;
;;   may introduce conflicts when arg is `x'
;;
;; + `defun-inline'
;;
;;   we could declaim a function as `inline' to make it
;;   expanded directly when calling rather than doing funcall
;;   to cut off some function calling time.
;;
;; + `defun-cached'
;;
;;   we could use a hash-table to cached the function results
;;   by function arguments: if arg is found in cache, return
;;   the cached value, otherwise, compute the value.
;;

(defmacro with-gensym (vars &body body)
  "Bind VARS list with gensym and evaluate BODY.

Syntax:

    (with-gensym ( var* ) . BODY)

"
  (assert (every #'symbolp vars))
  `(let ,(mapcar (lambda (var) `(,var ',(gensym (symbol-name var)))) vars)
     ,@body))

(defmacro defun-inline (name lambda-list &body body)
  "Define an inlined function NAME. "
  `(progn
     (declaim (inline ,name))
     (defun ,name ,lambda-list ,@body)))

(defmacro defun-cached (name lambda-list &body body)
  "Define a cached function called NAME.

Syntax:

    (defun-cached
      { NAME | ( NAME &key test (key (first LAMBDA-LIST)) fallback) }
         LAMBDA-LIST
      docstring?
      declaration*
      . body)

"
  (destructuring-bind (name &key (test 'eql) (key (first lambda-list)) fallback)
      (if (listp name) name (list name))
    (declare (type (member eql equal) test)
             (type symbol name))
    (with-gensym (cache keyv val fallbackv)
      `(let ((,cache (make-hash-table :test ',test))
             (,fallbackv ,fallback))
         (defun ,name ,lambda-list
           ,@(let ((docstring (pop body)))
               (cond ((stringp docstring) (list docstring))
                     (t (push docstring body) nil)))
           ,@(loop for expr = (pop body)
                   while (and (listp expr) (eq (car expr) 'declare))
                   collect expr
                   finally (push expr body))
           (let* ((,keyv ,key)
                  (,val  (gethash ,keyv ,cache ,fallbackv)))
             (if (equal ,val ,fallbackv)
                 (setf (gethash ,keyv ,cache) (progn ,@body))
                 ,val)))))))

;;; Iteration:
;; In Common Lisp, we have a very handy `loop' utility function:
;;
;;    (loop for i in list               ;; e1, e2, e3, ... if list is (e1 e2 e3 ...)
;;          for j from 1 below 20 by 2  ;; 1, 3, 5, 7, ...
;;          for k from 20 downto 0 by 4 ;; 20, 16, 12, 8, ...
;;          if test
;;            do expr
;;          do expr
;;          while test)
;;
;; These iteration macros are used as shortcuts of loop.
;;
;; *-dolist -> (*-dolist (elem list) &body)
;; *-repeat -> (*-repeat (i n) &body)
;;             (*-repeat (i n m step) &body)
;;

(defmacro or-dolist ((elem list) &body body)
  "Iter ELEM in LIST and return if BODY is true. "
  `(the boolean (loop for ,elem in ,list if (progn ,@body) return t)))

(defmacro and-dolist ((elem list) &body body)
  "Iter ELEM in LIST and return if BODY are all true. "
  `(the boolean (not (loop for ,elem in ,list if (not (progn ,@body)) return t))))

(defmacro and-repeat ((i n &optional m (step 1)) &body body)
  "Loop I from repeat N times, and logic and the BODY result.
Return t if all pass, nil if any fails.

Example:

    (repeat-and (i 20)     (evenp i)) ; => i = 0, 1, 2, ..., 19
    (repeat-and (i 2 20 2) (evenp i)) ; => i = 2, 4, 6, ..., 20
"
  `(the boolean
     ,(if m
          `(loop for ,i from ,n upto ,m by ,step
                 if (not (progn ,@body))
                   return nil
                 finally (return t))
          `(loop for ,i below ,n
                 if (not (progn ,@body))
                   return nil
                 finally (return t)))))

(defmacro windowed-dolist ((window size list &rest result) &body body)
  "Iter on LIST with each WINDOW as subsequence of LIST with SIZE. "
  (with-gensym (len lst shift window-size)
    `(loop with ,lst = ,list
           with ,window-size = ,size
           for ,len from (length ,lst) downto ,window-size
           for ,shift on ,lst
           for ,window = (subseq shift 0 ,window-size)
           do (progn ,@body)
           finally (return ,result))))

(defun windowed-mapcar (func window-size list &optional (step 1))
  "Like `mapcar' with WINDOW-SIZE for given FUNC on LIST. "
  (loop for len from (length list) downto window-size
        for shift on list by (curry #'nthcdr step)
        collect (apply func (subseq shift 0 window-size))))

(defun range-list (start end &optional (step 1))
  "Return a list of number of range (START END) by STEP. "
  (cond ((< step 0) (loop for i from start downto end by (abs step) collect i))
        ((> step 0) (loop for i from start upto   end by step       collect i))
        (t          (error "Step is zero. "))))

;;; Shortcuts:
;; nothing, just my coding flavour.

(defun-inline 2- (x)
  "Return X - 2. "
  (declare (type number x))
  (- x 2))

(defun-inline 2+ (x)
  "Return x + 2. "
  (+ 2 x))

(defun-inline 2* (x)
  "Return x * 2. "
  (* 2 x))

(defun-inline atomize (obj)
  "Return OBJ as atom. "
  (if (listp obj) (car obj) obj))

(defun-inline listfy (obj)
  "Return OBJ as list. "
  (if (atom obj) (list obj) obj))

;;; Functional Programming
;; In my opinion, when we call function programming, we
;; are referring computing not only values, but also the function
;; that return values.
;;

;; Function Compose
;; We can see a process as a chained function calling.
;; For example, a procedure:
;;
;;   (progn
;;     (do-this)
;;     (then-do-this))
;;
;; Can be written as:
;;
;;   (then-do-this (do-this))
;;
;; Assuming each `then-do-this' and `do-this' return an updated status.
;;

(defun compose (f g)
  "Return a function h(x) = f(g(x)). "
  (lambda (&rest args) (funcall f (apply g args))))

;; For performance concern, we could rewrite the expression
;; at compile time for better performance.

(define-compiler-macro compose (&whole form f g)
  "Rewriting Rules:
+ (compose f (compose g h)) -> (lambda (args) (f (g (h args))))
+ (compose (compose f g) h) -> (lambda (args) (f (g (h args))))
"
  (declare (ignore f g))
  (with-gensym (args)
    (labels ((extract (expr)
               (if (and (listp expr) (eq (first expr) 'compose))
                   (append (extract (second expr)) (extract (third expr)))
                   (list expr)))
             (expand (funcs)
               (if (endp (cdr funcs))
                   `(apply ,(car funcs) ,args)
                   `(funcall ,(car funcs) ,(expand (cdr funcs))))))
      `(lambda (&rest ,args) ,(expand (extract form))))))

;; This is a trivial implementation of arity.
;; In Common Lisp, a simple function lambda list is like:
;;
;;     (lambda (x y z))
;;     (lambda (x &optional y))
;;     (lambda (y &key k1 k2))
;;     (lambda (&rest args))
;;     (lambda (y &key key1 &allow-other-keys))
;;

(defun args (&rest args)
  "Return input arguments as list. "
  args)

(defun nth-arg (n)
  "Return a function that pick Nth argument of input arguments. "
  (lambda (&rest args) (nth n args)))

(defun nth-arg* (&rest ns)
  "Return NS elements of input arguments as list. "
  (lambda (&rest args) (mapcar (rcurry #'nth args) ns)))

;; The curry is a interesting mechanics especially when you
;; want to write some fancy code like:
;;
;;    (mapcar (curry  #'nth 2) list)        ; => (mapcar #'second list)
;;    (mapcar (rcurry #'nth list) '(1 2 3)) ; => ((nth 1 list) (nth 2 list) (nth 3 list))
;;

(defun curry (func arg)
  "Left curry FUNC with ARG. "
  (lambda (&rest args) (apply func (cons arg args))))

(defun curry* (func &rest arg)
  "Left curry FUNC with ARGS. "
  (lambda (&rest args) (apply func (append arg args))))

(defun rcurry (func arg)
  "Return a function of g(args) = f(args, arg). "
  (lambda (&rest args) (apply func (append args (list arg)))))

(defun rcurry* (func &rest arg*)
  "Return a function of g(args) = f(args, arg). "
  (lambda (&rest args) (apply func (append args arg*))))

;;; Data Structure
;; An alist is a list of elements (key . value). You can use `assoc' to
;; get element by the key:
;;
;;    (assoc 'a '((a . 1) (b . 2))) ; => (a . 1)
;;
;; However, when the alist size got larger, it's not so performance
;; fetching elements from list data structure, so switching to hash-table
;; would be more efficiency.
;;
;; Note that there's other key-value pair data structure called plist
;; constructed by list:
;;
;;    (getf '(:a 1 :b 2) :b) ; => 2
;;
;; And if you are storing a data structure with fixed size of elements,
;; maybe using array would bring better performance.
;;

(defun alist<-hash-table (hash-table)
  "Turn HASH-TABLE to ALIST.
Return an alist of HASH-TABLE's key and value. "
  (declare (type hash-table hash-table))
  (let ((alist ()))
    (maphash (lambda (k v) (push (cons k v) alist)) hash-table)
    alist))

(defun hash-table<-alist (alist &key hash-table (test 'eql) (if-exist :replace) fallback)
  "Turn ALIST into HASH-TABLE.
Return a HASH-TABLE.

Parameters:
+ ALIST: an alist like ((key . val))
+ HASH-TABLE: if not given, create a new hash-table of type TEST
+ TEST: either `eql' or `equal'
+ IF-EXIST: if already exists in hash table, resolve conflicts
  if is a function, it should be a function like (lambda (prev curr) new)
+ FALLBACK: default fallback value of `gethash'.
"
  (declare (type list alist)
           (type (member eql equal) test)
           (type (or function (member :replace :keep)) if-exist))
  (let ((hash-table (if (hash-table-p hash-table) hash-table
                        (make-hash-table :test test)))
        (if-exist   (if (functionp if-exist) if-exist
                        (ecase if-exist
                          (:replace (nth-arg 1))
                          (:keep    (nth-arg 0))))))
    (loop for (key . val) in alist
          for prev = (gethash key hash-table fallback)
          do (setf (gethash key hash-table)
                   (if (equal fallback prev) val
                       (funcall if-exist prev val)))
          finally (return hash-table))))

(defun alist-reduce (function alists &key (test 'eql) fallback)
  "Reduce on alist key with function.
Return a new alist.

Parameters:
+ FUNCTION: the function used to reduce (lambda (prev curr) new)
+ ALISTS: a list of alists
+ TEST: how the key is hashed (eql or equal)
+ FALLBACK: see `hash-table<-alist'
"
  (declare (type function function)
           (type list alists)
           (type (member eql equal) test))
  (alist<-hash-table
   (reduce (lambda (hash alist)
             (hash-table<-alist alist :test       test
                                      :if-exist   function
                                      :fallback   fallback
                                      :hash-table hash))
           alists
           :initial-value (make-hash-table :test test))))

(defun group (sequence &key (key #'identity) (reduce #'cons) (test 'equal) initial-value)
  "Group elements in SEQUENCE.

Parameters:
+ SEQUENCE: a `list', `array' or so sequence
+ KEY: apply KEY on element as hash key
  should be a function with lambda-list:

    (lambda (elem) return-value-as-elem-compare-key)

+ TEST: the grouping hash
  should be `eql' or `equal' (like `make-hash-table')

+ REDUCE: how the grouped value is reduced with new element,
  should be a function with lambda-list:

    (lambda (new old) return-value-as-old)

+ INITIAL-VALUE: the init OLD value (default as `nil')

Example:

    (group '(1 2 1 2 3)) ; => ((3 . (3)) (2 . (2 2)) (1 . (1 1)))

"
  (declare (type sequence sequence)
           (type (function (t) *)    key)
           (type (member eql equal)     test)
           (type (function (t t) *) reduce))
  (let ((group (make-hash-table :test test)))
    (map 'nil (lambda (elem)
                (let ((key (funcall key elem)))
                  (setf (gethash key group)
                        (funcall reduce elem (gethash key group initial-value)))))
         sequence)
    (alist<-hash-table group)))


;;; Problem 1. Multiples of 3 or 5
;; If we list all the natural numbers below 10 that are multiples of 3
;; or 5, we get 3, 5, 6 and 9. The sum of these multiples is 23.
;;
;; Find the sum of all the multiples of 3 or 5 below 1000.
;;

;; Definition:
;; If NUMBER can be moded by divisor, NUMBER mod DIVISOR is 0.

(defun-inline modp (number divisor)
  "Test if NUMBER can be moded by DIVISOR. "
  (declare (type integer number divisor))
  (zerop (mod number divisor)))

(defun problem1 (&optional (dividers '(3 5)) (max 1000))
  "Find the sum of all the multiples of 3 or 5 below 1000. "
  (loop for n from 3 below max
        if (or-dolist (d dividers) (modp n d)) sum n))


;;; Problem 2. Even Fibonacci Numbers
;; Each new term in the Fibonacci sequence is generated by adding
;; the previous two terms. By starting with 1 and 2, the first
;; 10 terms will be:
;;
;;    1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...
;;
;; By considering the terms in the Fibonacci sequence whose values
;; do not exceed four million, find the sum of the even-valued
;; terms.
;;

;; Definition:
;; Fib(1) = 1
;; Fib(2) = 2
;; Fib(n) = Fib(n - 1) + Fib(n - 2)

(defun-cached fibonacci (n)
  "Return Nth Fibonacci number. "
  (declare (type positive-integer n))
  (if (<= n 2)
      n
      (+ (fibonacci (1- n))
         (fibonacci (2- n)))))

;; Note: it would be much more slower if using fibonacci
;; without cached implementation.

(defun problem2 (&optional (max 4000000))
  "Find the sum of the even Fibonacci number below MAX. "
  (loop for n from 1
        for fib = (fibonacci n)
        while (< fib max)
        if (evenp fib)
          sum fib))

;; Reuse the fibonacci number when increasing, this is
;; faster as hashing time is skipped.

(defun problem2-faster (&optional (max 4000000))
  "Find the sum of the even Fibonacci number below MAX. "
  (loop with f1 = 1
        with f2 = 2
        while (< f2 max)
        if (evenp f2)
          sum f2
        do (shiftf f1 f2 (+ f1 f2))))


;;; Problem 3. Largest Prime Factor
;; The prime factors of 13195 are 5, 7, 13 and 29.
;;
;; What is the largest prime factor of the number 600851475143?
;;

;; Definition:
;; nth-prime(1) = 2
;; nth-prime(2) = 3
;; nth-prime(n) = next prime starting from nth-prime(n - 1)

(defun-cached nth-prime (nth)
  "Return Nth prime. "
  (declare (type positive-integer nth))
  (cond ((= nth 1) 2)
        ((= nth 2) 3)
        (t (loop for p from (2+ (nth-prime (1- nth))) by 2
                 if (primep p) return p))))

;; Definition:
;; If a number can be divided into prod(pi^ni), it is not a prime,
;; otherwise, is a prime.
;;
;; So n is not a prime if all primes less then sqrt(n)
;; cannot mod n (not (modp n p)).
;;
;; And 1 is not prime.
;;

(defun-cached (primep :fallback :null) (n)
  "Test if N is prime number. "
  (declare (type natural n))
  (and (/= n 1)
       (loop with max = (truncate (sqrt n))
             for i from 1
             for p = (nth-prime i)
             while (<= p max)
             if (modp n p)
               return nil
             finally (return t))))

(defun problem3 (&optional (n 600851475143))
  "Find the largest prime factor of the number N. "
  (declare (type unsigned-byte n))
  (loop for div from (truncate (sqrt n)) downto 2
        if (and (modp n div) (primep div))
          return div))

;; Note: here's another approach:

;; Definition:
;; prime-factor-list(n) = (n) if n is prime
;; prime-factor-list(n) = append of
;;   prime-factor-list(a), prime-factor-list(b) if n = a * b

(defun-cached prime-factor-list (n)
  "Return a list of prime factors for number N. "
  (declare (type natural n))
  (loop for div from (truncate (sqrt n)) downto 2
        if (modp n div)
          return (append (prime-factor-list div)
                         (prime-factor-list (/ n div)))
        finally (return (when (/= n 1) (list n)))))

;; Much slower when N is very large.

;; (defun factors-slower (n)
;;   "Return a list of (factor . order) for number N. "
;;   (loop for i from 1
;;         for p from (nth-prime i)
;;         if (modp n p)
;;           collect (loop with order = 0
;;                         do (setf n (/ n p))
;;                         do (incf order)
;;                         while (modp n p)
;;                         finally (return (cons p order)))
;;         while (/= n 1)))

(defun factors (n)
  "Return a list of (factor . order) for number N. "
  (declare (type natural n))
  (group (prime-factor-list n)
         :reduce (lambda (- order) (1+ order))
         :initial-value 0))

(defun problem3-other-way (&optional (n 600851475143))
  "Find the largest prime factor of the number N. "
  (car (first (sort (factors n) #'> :key #'car))))


;;; Problem 4. Largest Palindrome Product
;; A palindromic number reads the same both ways. The largest palindrome
;; made from the product of two 2-digit numbers is 9009 = 91 * 99.
;;
;; Find the largest palindrome made from the product of two 3-digit numbers.
;;

;; Here introduced the p-based number expression.

;; Notation:
;; n = sum({ p^ei * ai })

(defun-inline p-shift (n &optional (base 10))
  "Shift number N under BASE. "
  (declare (type unsigned-byte n base))
  (floor n base))

(defun-inline p-left-shift (n &optional (base 10))
  "Left shift number N under BASE. "
  (declare (type unsigned-byte n base))
  (* n base))

;; So for p-shift (right):
;; p-shift(sum({ p^ei * ai })) = sum({ p^(ei - 1) * ai })
;;
;; If n = 0, p-digit(n) = '(0)
;; If n /= 0, p-digit(n) = p-digit(p-shift(n)), n mod base
;;

(defun p-digits (n &optional (base 10))
  "Return a list of digits for number N under BASE. "
  (declare (type unsigned-byte n))
  (if (zerop n) '(0)
      (loop with p-digit = ()
            for v = n then (p-shift v base) until (zerop v)
            do (push (mod v base) p-digit)
            finally (return p-digit))))

;; Definition:
;; If a sequence is palindromic,
;; sequence(i) = sequence(length(sequence) - i)
;;

(defun palindromic-sequence-p (sequence &optional (test #'=))
  "Test if SEQUENCE is palindromic.
Return t or nil.

Parameters:
+ SEQUENCE: a sequence to"
  (declare (type sequence sequence)
           (type function test))
  ;; convert sequence as simple vector to accelerate
  (let* ((arr   (coerce sequence 'simple-vector))
         (len   (length arr))
         (len-1 (1- len)))
    (and-repeat (i (floor len 2))
      (funcall test (svref arr i) (svref arr (- len-1 i))))))

(defun palindromep (n &optional (base 10))
  "Test if N is palindrome number under BASE. "
  (palindromic-sequence-p (p-digits n base)))

;; A palindrome number can be considered as:
;;
;;    100000 * a + 10000 * b + 1000 * c + 100 * c + 10 * b + a
;;
;; => 100001 * a + 10010 * b + 1100 * c
;; => 11 * (9091 * a + 910 * b + 100 * c)
;;
;; so the `j' loop would search on number that moded by 11.
;; cannot reduce much computing cost.
;;

(defun problem4 ()
  "Return the largest palindrome made from the product of two 3-digit numbers. "
  (let ((products ()))
    (loop for i from 999 downto 100 do
      (loop for j from (* 11 (floor i 11)) downto 110 by 11
            for n = (* i j)
            if (palindromep n)
              do (push n products)))
    (first (sort products #'>))))



;;; Problem 5. Smallest Multiple
;; 2520 is the smallest number that can be divided by each of the numbers
;; from 1 to 10 without any remainder.
;;
;; What is the smallest positive number that is evenly divisible by all
;; the numbers from 1 to 20?
;;

;; This is like the inverse function of `factors'.

(defun int<-factors (factors)
  "Turn list ((factor . order)) into integer. "
  (the integer
    (reduce (lambda (mul factor-order)
              (destructuring-bind (factor . order) factor-order
                (* mul (expt factor order))))
            factors
            :initial-value 1)))

;; If N is divided by M, the factors of N and M would have same factor
;; and every factor order of M should less or equal to factor order of
;; N.
;;

(defun problem5 (&optional (max 20))
  "Return the smallest positive number that is evenly divisible by
the numbers from 1 to MAX. "
  (int<-factors (alist-reduce #'max (mapcar #'factors (range-list 2 max)))))



;;; Problem 6. Sum Square Difference
;; The sum of the squares of the first ten natural numbers is,
;;
;;    1^2 + 2^2 + ... + 10^2 = 385
;;
;; The square of the sum of the first ten natural numbers is,
;;
;;    (1 + 2 + ... + 10)^2 = 55^2 = 3025
;;
;; Hence the difference between the sum of the squares of the
;; first ten natural numbers and the square of the sum is
;; 3025 - 385 = 2640.
;;
;; Find the difference between the sum of the squares of the
;; first one hundred natural numbers and the square of the
;; sum.

(defun-inline square (x)
  "Return square of X. "
  (declare (type number x))
  (* x x))

(defun sum-of-squares (sequence)
  "Return sum of squares of NUMS. "
  (reduce #'+ (map 'list #'square sequence)))

(defun sum (sequence)
  "Return sum of SEQUENCE. "
  (let ((sum 0))
    (map nil (lambda (x) (incf sum x)) sequence)
    sum))

(defun problem6 (&optional (max 100))
  "Return the difference sum of the squares and square of the sum. "
  (let ((nums (range-list 1 max)))
    (abs (- (sum-of-squares nums) (square (sum nums))))))



;;; Problem 7. 10001st Prime
;; By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13,
;; we can see that the 6th prime is 13.
;;
;; What is the 10001st prime number.

(defun problem7 (&optional (nth 10001))
  "Return the NTH prime number. "
  (nth-prime nth))


;;; Problem 8. Largest Product in a Series
;; The four adjacent digits in the 1000-digit number that have
;; the greatest product are 9 * 9 * 8 * 9 = 5832.
;;
;; 73167176531330624919225119674426574742355349194934
;; 96983520312774506326239578318016984801869478851843
;; 85861560789112949495459501737958331952853208805511
;; 12540698747158523863050715693290963295227443043557
;; 66896648950445244523161731856403098711121722383113
;; 62229893423380308135336276614282806444486645238749
;; 30358907296290491560440772390713810515859307960866
;; 70172427121883998797908792274921901699720888093776
;; 65727333001053367881220235421809751254540594752243
;; 52584907711670556013604839586446706324415722155397
;; 53697817977846174064955149290862569321978468622482
;; 83972241375657056057490261407972968652414535100474
;; 82166370484403199890008895243450658541227588666881
;; 16427171479924442928230863465674813919123162824586
;; 17866458359124566529476545682848912883142607690042
;; 24219022671055626321111109370544217506941658960408
;; 07198403850962455444362981230987879927244284909188
;; 84580156166097919133875499200524063689912560717606
;; 05886116467109405077541002256983155200055935729725
;; 71636269561882670428252483600823257530420752963450
;;
;; Find the thirteen adjacent digits in the 1000-digit
;; number that have the greatest product. What is the
;; value of this product?
;;

(defun digit<-digit-char (char)
  "Turn CHAR (#\0 to #\9) into integer number. "
  (the (integer 0 9) (- (char-code char) (char-code #\0))))

(defun prod (sequence)
  "Return the products of SEQUENCE. "
  (let ((prod 1))
    (map nil (lambda (x) (setf prod (* prod x))) sequence)
    prod))

(defun problem8 (&optional
                 (len 13)
                 (digits (mapcar #'digit<-digit-char
                                 (concatenate
                                  'list
                                  "73167176531330624919225119674426574742355349194934"
                                  "96983520312774506326239578318016984801869478851843"
                                  "85861560789112949495459501737958331952853208805511"
                                  "12540698747158523863050715693290963295227443043557"
                                  "66896648950445244523161731856403098711121722383113"
                                  "62229893423380308135336276614282806444486645238749"
                                  "30358907296290491560440772390713810515859307960866"
                                  "70172427121883998797908792274921901699720888093776"
                                  "65727333001053367881220235421809751254540594752243"
                                  "52584907711670556013604839586446706324415722155397"
                                  "53697817977846174064955149290862569321978468622482"
                                  "83972241375657056057490261407972968652414535100474"
                                  "82166370484403199890008895243450658541227588666881"
                                  "16427171479924442928230863465674813919123162824586"
                                  "17866458359124566529476545682848912883142607690042"
                                  "24219022671055626321111109370544217506941658960408"
                                  "07198403850962455444362981230987879927244284909188"
                                  "84580156166097919133875499200524063689912560717606"
                                  "05886116467109405077541002256983155200055935729725"
                                  "71636269561882670428252483600823257530420752963450"))))
  "Find the greatest LEN digits. "
  (reduce #'max (windowed-mapcar (compose #'prod #'args) len digits)))



;;; Problem 9. Special Pythagorean Triplet
;; A Pythagorean triplet is a set of three natural numbers,
;; a < b < c, for which,
;;
;;    a^2 + b^2 = c^2
;;
;; For example, 3^2 + 4^2 = 9 + 16 = 25 = 5^2.
;;
;; These exists exactly one Pythagorean triplet for which a + b + c = 1000.
;; Find the product a * b * c.
;;

(defmacro with-sorted3 ((a b c) &body body)
  "Sort A, B, C and evaluate BODY. "
  (with-gensym (min mid max)
    `(let* ((,min (min ,a ,b ,c))
            (,max (max ,a ,b ,c))
            (,mid (- (+ ,a ,b ,c) (+ ,min ,max)))
            (,a ,min)
            (,b ,mid)
            (,c ,max))
       ,@body)))

(defun pythagoreanp (a b c)
  "Test if A, B, C is a set of Pythagorean number. "
  (with-sorted3 (a b c)
    (= (+ (square a) (square b)) (square c))))

;; a + b + c = 1000
;; a^2 + b^2 = c^2
;; => b = ((2 * a - n) * n) / (2 * (a - n))

(defun problem9 (&optional (sum 1000))
  "Find the Pythagorean a + b + c = 1000 and return a * b * c. "
  (loop for a from 1 upto (floor sum 2)
        for b1 = (* (- (* 2 a) sum) sum)
        for b2 = (* 2 (- a sum))
        if (modp b1 b2)
          return (let* ((b (/ b1 b2))
                        (c (- sum a b)))
                   (* a b c))))


;;; Problem 10. Summation of Primes
;; The sum of the primes below 10 is 2 + 3 + 5 + 7 = 17.
;;
;; Find the sum of all the primes below two million.

(defun problem10 (&optional (max (* 2 +million+)))
  "Find the sum of all the primes below MAX. "
  (loop for n from 2 below max
        if (primep n) sum n))



;;; Problem Largest Product in a Grid
;; In the 20 * 20 grid below, what is the greatest product of
;; four adjacent numbers in the same direction (up, down, left,
;; right, or diagonally) in the 20x20 grid.
;;

(defun grid-lr (grid i j &optional (len 4))
  "Return a list of GRID element starting at I, J
of length LEN at direction LR. "
  (declare (type (array t 2) grid)
           (type unsigned-byte i j len))
  (destructuring-bind (imax jmax) (array-dimensions grid)
    (assert (and (<= 0 i) (< i (- imax len))
                 (<= 0 j) (< j jmax)))
    (loop for ii from i below (+ i len)
          collect (aref grid ii j))))

(defun grid-ud (grid i j &optional (len 4))
  "Return a list of GRID element starting at I, J
of length LEN at direction UD. "
  (declare (type (array t 2) grid)
           (type unsigned-byte i j len))
  (destructuring-bind (imax jmax) (array-dimensions grid)
    (assert (and (<= 0 i) (< i imax)
                 (<= 0 j) (< j (- jmax len))))
    (loop for jj from j below (+ j len)
          collect (aref grid i jj))))

(defun grid-trig (grid i j &optional (len 4))
  "Return a list of GRID element starting at I, J
of length LEN at direction diagonally. "
  (declare (type (array t 2) grid)
           (type unsigned-byte i j len))
  (destructuring-bind (imax jmax) (array-dimensions grid)
    (assert (and (<= 0 i) (< i (- imax len))
                 (<= 0 j) (< j (- jmax len))))
    (loop for ii from i below (+ i len)
          for jj from j below (+ j len)
          collect (aref grid ii jj))))

(defun problem11 (&optional (len 4) (grid
                                     #2A((01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48)
                                         (20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54)
                                         (20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16)
                                         (04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36)
                                         (88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69)
                                         (04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66)
                                         (19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40)
                                         (86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58)
                                         (16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57)
                                         (78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92)
                                         (21 36 23 09 75 00 76 44 20 45 35 14 00 61 33 97 34 31 33 95)
                                         (24 55 58 05 66 73 99 26 97 17 78 78 96 83 14 88 34 89 63 72)
                                         (67 26 20 68 02 62 12 20 95 63 94 39 63 08 40 91 66 49 94 21)
                                         (32 98 81 28 64 23 67 10 26 38 40 67 59 54 70 66 18 38 64 70)
                                         (24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50)
                                         (22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80)
                                         (52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91)
                                         (81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65)
                                         (49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00)
                                         (08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08))))
  "Return the greatest product of four adjacent numbers. "
  (let ((prod 0))
    (destructuring-bind (imax jmax) (array-dimensions grid)
      (loop for i from 0 below (- imax len) do
        (loop for j from 0 below (- jmax len) do
          (setf prod (max prod
                          (prod (grid-lr   grid i j len))
                          (prod (grid-ud   grid i j len))
                          (prod (grid-trig grid i j len)))))))
    prod))



;;; Problem 12. Highly Divisible Triangular Number
;; The sequence of triangle numbers is generated by adding the natural
;; numbers. So the 7th triangle number would be 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28.
;; The first ten terms would be:
;;
;;     1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...
;;
;; Let us list the factors of the first seven triangle numbers:
;;
;;         1: 1
;;         3: 1, 3
;;         6: 1, 2, 3, 6
;;        10: 1, 2, 5, 10
;;        15: 1, 3, 5, 15
;;        21: 1, 3, 7, 21
;;        28: 1, 2, 4, 7, 14, 28
;;
;; We can see that 28 is the first triangle number to have over five
;; divisors.
;;
;; What is the value of the first triangle number to have over five
;; hundred divisors.
;;

;; Algorithm:
;; divisors(1)     = (1)
;; divisors(n * p^m) = (append
;;                       (mapcar (curry #'* p^0) divisors(n))
;;                       (mapcar (curry #'* p^1) divisors(n))
;;                       (mapcar (curry #'* p^2) divisors(n))
;;                       ...)
;;
;; Note that all number could be splited as n = p1^n1 * p2^n2 ...,
;; so this procedure is terminatable.
;;

(defun divisors (n)
  "Return a list of divisors of N. "
  (declare (type unsigned-byte n))
  (loop for divisors = '(1) then (apply #'append (cons divisors mul))
        for (factor . order) in (factors n)
        for mul = (loop for i from 1 upto order
                        collect (mapcar (curry #'* (expt factor i)) divisors))
        finally (return divisors)))

(defun problem12 (&optional (max 500))
  "Return the value of the first triangle number to have over MAX divisors. "
  (loop for i from 1
        for trig = (* (+ 1 i) i 1/2)
        if (> (length (divisors trig)) max)
          return trig))

;; a faster implementation of (length (divisors n))

;; Notice that for n = p1^n1 * p2^n2 * ..., any number
;; n' = p1^n1' * p2^n2' * ..., (n1' <= n1, n2' <= n2, ...)
;; can divide n. (aka. (modp n n') is true).
;;
;; So the number of dividors of n can be calculated by:
;; (1 + n1) * (1 + n2) * ...
;;

(defun count-divisors (n)
  "Return the number of N divisors. "
  (prod (mapcar (compose #'1+ #'cdr) (factors n))))

(defun problem12-faster (&optional (max 500))
  "Return the value of the first triangle number to have over MAX divisors. "
  (loop for i from 1
        for trig = (* (+ 1 i) i 1/2)
        if (> (count-divisors trig) max)
          return trig))


;;; Problem 13. Large Sum
;; Work out the first ten digits of the sum of the following 50 digits numbers.

(defun int<-p-digits (digits &optional (base 10))
  "Return integer of DIGITS of BASE. "
  (loop with int = 0
        for digit in digits
        do (setf int (+ (* base int) digit))
        finally (return int)))

(defun problem13 (&optional (n 10) (digits
                                    '(37107287533902102798797998220837590246510135740250
                                      46376937677490009712648124896970078050417018260538
                                      74324986199524741059474233309513058123726617309629
                                      91942213363574161572522430563301811072406154908250
                                      23067588207539346171171980310421047513778063246676
                                      89261670696623633820136378418383684178734361726757
                                      28112879812849979408065481931592621691275889832738
                                      44274228917432520321923589422876796487670272189318
                                      47451445736001306439091167216856844588711603153276
                                      70386486105843025439939619828917593665686757934951
                                      62176457141856560629502157223196586755079324193331
                                      64906352462741904929101432445813822663347944758178
                                      92575867718337217661963751590579239728245598838407
                                      58203565325359399008402633568948830189458628227828
                                      80181199384826282014278194139940567587151170094390
                                      35398664372827112653829987240784473053190104293586
                                      86515506006295864861532075273371959191420517255829
                                      71693888707715466499115593487603532921714970056938
                                      54370070576826684624621495650076471787294438377604
                                      53282654108756828443191190634694037855217779295145
                                      36123272525000296071075082563815656710885258350721
                                      45876576172410976447339110607218265236877223636045
                                      17423706905851860660448207621209813287860733969412
                                      81142660418086830619328460811191061556940512689692
                                      51934325451728388641918047049293215058642563049483
                                      62467221648435076201727918039944693004732956340691
                                      15732444386908125794514089057706229429197107928209
                                      55037687525678773091862540744969844508330393682126
                                      18336384825330154686196124348767681297534375946515
                                      80386287592878490201521685554828717201219257766954
                                      78182833757993103614740356856449095527097864797581
                                      16726320100436897842553539920931837441497806860984
                                      48403098129077791799088218795327364475675590848030
                                      87086987551392711854517078544161852424320693150332
                                      59959406895756536782107074926966537676326235447210
                                      69793950679652694742597709739166693763042633987085
                                      41052684708299085211399427365734116182760315001271
                                      65378607361501080857009149939512557028198746004375
                                      35829035317434717326932123578154982629742552737307
                                      94953759765105305946966067683156574377167401875275
                                      88902802571733229619176668713819931811048770190271
                                      25267680276078003013678680992525463401061632866526
                                      36270218540497705585629946580636237993140746255962
                                      24074486908231174977792365466257246923322810917141
                                      91430288197103288597806669760892938638285025333403
                                      34413065578016127815921815005561868836468420090470
                                      23053081172816430487623791969842487255036638784583
                                      11487696932154902810424020138335124462181441773470
                                      63783299490636259666498587618221225225512486764533
                                      67720186971698544312419572409913959008952310058822
                                      95548255300263520781532296796249481641953868218774
                                      76085327132285723110424803456124867697064507995236
                                      37774242535411291684276865538926205024910326572967
                                      23701913275725675285653248258265463092207058596522
                                      29798860272258331913126375147341994889534765745501
                                      18495701454879288984856827726077713721403798879715
                                      38298203783031473527721580348144513491373226651381
                                      34829543829199918180278916522431027392251122869539
                                      40957953066405232632538044100059654939159879593635
                                      29746152185502371307642255121183693803580388584903
                                      41698116222072977186158236678424689157993532961922
                                      62467957194401269043877107275048102390895523597457
                                      23189706772547915061505504953922979530901129967519
                                      86188088225875314529584099251203829009407770775672
                                      11306739708304724483816533873502340845647058077308
                                      82959174767140363198008187129011875491310547126581
                                      97623331044818386269515456334926366572897563400500
                                      42846280183517070527831839425882145521227251250327
                                      55121603546981200581762165212827652751691296897789
                                      32238195734329339946437501907836945765883352399886
                                      75506164965184775180738168837861091527357929701337
                                      62177842752192623401942399639168044983993173312731
                                      32924185707147349566916674687634660915035914677504
                                      99518671430235219628894890102423325116913619626622
                                      73267460800591547471830798392868535206946944540724
                                      76841822524674417161514036427982273348055556214818
                                      97142617910342598647204516893989422179826088076852
                                      87783646182799346313767754307809363333018982642090
                                      10848802521674670883215120185883543223812876952786
                                      71329612474782464538636993009049310363619763878039
                                      62184073572399794223406235393808339651327408011116
                                      66627891981488087797941876876144230030984490851411
                                      60661826293682836764744779239180335110989069790714
                                      85786944089552990653640447425576083659976645795096
                                      66024396409905389607120198219976047599490197230297
                                      64913982680032973156037120041377903785566085089252
                                      16730939319872750275468906903707539413042652315011
                                      94809377245048795150954100921645863754710598436791
                                      78639167021187492431995700641917969777599028300699
                                      15368713711936614952811305876380278410754449733078
                                      40789923115535562561142322423255033685442488917353
                                      44889911501440648020369068063960672322193204149535
                                      41503128880339536053299340368006977710650566631954
                                      81234880673210146739058568557934581403627822703280
                                      82616570773948327592232845941706525094512325230608
                                      22918802058777319719839450180888072429661980811197
                                      77158542502016545090413245809786882778948721859617
                                      72107838435069186155435662884062257473692284509516
                                      20849603980134001723930671666823555245252804609722
                                      53503534226472524250874054075591789781264330331690)))
  "Return the first N digits. "
  (int<-p-digits (subseq (p-digits (sum digits)) 0 n)))


;;; Problem 14. Longest Collatz Sequence
;; The following iterative sequence is defined for the set of
;; positive integers:
;;
;;   n -> n / 2     (n is even)
;;   n -> 3 * n + 1 (n is odd)
;;
;; Using the rule above and starting with 13, we generate the following
;; sequence:
;;
;;   13 -> 40 -> 20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1
;;
;; It can be seen that this sequence (starting at 13 and finishing at 1)
;; contains 10 terms.
;; Although it has not been proved yet (Collatz Problem), it is thought
;; that all starting numbers finish at 1.
;;
;; Which starting number under one million, produces the longest chain?
;;
;; NOTE: Once the chain starts the terms are allowed to go above one
;; million.
;;

(defun collatz-next (start)
  "Return next of START of Collatz sequence. "
  (if (evenp start)
      (/ start 2)
      (1+ (* 3 start))))

(defun-cached collatz-list (start)
  "Return a Collatz List starting from START. "
  (if (= start 1) '(1)
      (cons start (collatz-list (collatz-next start)))))

(defun-cached count-collatz-list (start)
  "Return the length of Collatz List starting from START. "
  (if (= start 1) 1 (1+ (count-collatz-list (collatz-next start)))))

(defun problem14 (&optional (lim (* 1 +million+)))
  "Return the number below LIM of the longest Collatrz list. "
  (loop with start = 1
        with max   = 1
        for i from 1 below lim
        for cnt = (count-collatz-list i)
        if (> cnt max)
          do (setf max   cnt
                   start i)
        finally (return start)))


;;; Problem 15. Lattice Paths
;; Starting in the top left corner of a 2x2 grid, and only being
;; able to move to the right and down, there are exactly 6 routes
;; to the bottom right corner.
;;

(defmacro at (grid &rest indexs)
  "Get element of GRID by INDEXS.

Example:

    (at grid x)
    (at grid x y)
    (at grid x y z)

"
  `(aref ,grid ,@(reverse indexs)))

;; The path length is:
;;
;;    (path i j) = (+ (path (1+ i) j) (path i (1+ j)))
;;
;; use `cache` to acclerate iteration

(defun problem15 (&optional (w 20) (h 20))
  "Return the counts of routes through a WxH grid. "
  (let ((cache (make-array (list (1+ h) (1+ w)) :initial-element -1)))
    (setf (at cache w h) 1)
    (labels ((path (i j)
               (if (>= (at cache i j) 0)
                   (at cache i j)
                   (setf (at cache i j)
                         (+ (if (= i w) 0
                                (path (1+ i) j))
                            (if (= j h) 0
                                (path i (1+ j))))))))
      (path 0 0))))


;;; Problem 16. Power Digit Sum
;; 2^15 = 32768 and the sum of its digits is 3 + 2 + 7 + 6 + 8 = 26.
;;
;; What is the sum of the digits of the number 2^1000?
;;

(defun problem16 (&optional (exp 1000))
  (sum (p-digits (expt 2 exp))))


;;; Problem 17. Number Letter Counts
;; If the numbers 1 to 5 are written out in words: one, two, three,
;; four, five, then there are 3 + 3 + 5 + 4 + 4 = 19 letters used in total.
;;
;; If all the numbers from 1 to 1000 (one thousand) inclusive were
;; written out in words, how many letters would be used?
;;
;; Note: Do not count spaces or hyphens.
;; For example, 342 (three hundred and forty-two) contains 23 leters
;; and 115 (one hundred and fifteen) contains 20 letters.
;; The use of "and" when writing out numbers is in compliance with
;; British usage.
;;

(defun constr (&rest sequences)
  "Merge SEQUENCES as a string. "
  (apply #'concatenate 'string sequences))

(defun number<100-to-words (number)
  "Turn NUMBER (< 100) as english words. "
  (declare (type unsigned-byte number))
  (assert (<= 0 number 99))
  (let ((map10 #("" "" "twenty" "thirty" "forty" "fifty" "sixty" "seventy" "eighty" "ninety"))
        (map1  #("zero" "one" "two" "three" "four" "five" "six" "seven" "eight" "nine"
                 "ten" "eleven" "twelve" "thirteen" "fourteen" "fifteen" "sixteen"
                 "seventeen" "eighteen" "nineteen")))
    (if (< number 20)
        (aref map1 number)
        (let ((d10 (floor (/ number 10)))
              (d1  (mod number 10)))
          (constr (aref map10 d10) "-" (aref map1 d1))))))

(defun number<1000-to-words (number)
  "Turn NUMBER (< 1000) as english words. "
  (declare (type unsigned-byte number))
  (assert (<= 0 number 999))
  (let ((map1 #("zero" "one" "two" "three" "four" "five" "six" "seven" "eight" "nine")))
    (let ((d100 (floor (/ number 100)))
          (d10  (mod number 100)))
      (cond ((zerop d100) (number<100-to-words d10))
            ((zerop d10)  (constr (aref map1 d100) " hundred"))
            (t (constr (aref map1 d100) " hundred and " (number<100-to-words d10)))))))

(defun number-to-words (number)
  "Turn NUMBER as english words. "
  (let ((map1000 #(nil "thousand" "million" "billion" "trillion"
                   "quadrillion"  "quintillion"       "sextillion"
                   "septillion"   "octillion"         "nonillion"
                   "decillion"    "undecillion"       "duodecillion"
                   "tredecillion" "quattuordecillion" "quindecillion"
                   "sexdecillion" "septendecillion"   "octodecillion"))
        (digits  (p-digits number 1000)))
    (if (zerop number) "zero"
        (loop for i from (- (length digits) 1) downto 0
              for digit in digits
              for unit = (aref map1000 i)
              if (not (zerop digit))
                collect (if unit
                            (constr (number<1000-to-words digit) " " unit)
                            (number<1000-to-words digit))
                  into words
              finally (return (format nil "~{~A~^ ~}" words))))))

(defun count-letters (string)
  "Count letters in STRING. "
  (let ((count 0))
    (dotimes (i (length string) count)
      (let ((c (aref string i)))
        (when (or (char<= #\A c #\Z) (char<= #\a c #\z))
          (incf count))))))

(defun problem17 (&optional (max 1000))
  "Return the number of letters of words. "
  (loop for i from 1 upto max sum (count-letters (number-to-words i))))


;;; Problem 18. Maximum Path Sum I
;; By starting at the top of the triangle below and moving to adjacent
;; numbers on the row below, the maximum total from top to bottom is 23.
;;
;;                *3*
;;              *7*  4
;;             2  *4*  6
;;           8  5  *9*  3
;;
;; That is, 3 + 7 + 4 + 9 = 23.
;;
;; Find the maximum total from top to bottom of the triangle below:
;;

;; To solve this, just calculate them all and using the array as cache.
;;
;;     (path-length layer i) <= (max (trig (1+ layer) i) (trig (1+ layer) (1+ i)))
;;
;; So going from bottom to top, thus the result can reduced.
;;

(defun problem18 (&optional (trig '((75)
                                    (95 64)
                                    (17 47 82)
                                    (18 35 87 10)
                                    (20 04 82 47 65)
                                    (19 01 23 75 03 34)
                                    (88 02 77 73 07 63 67)
                                    (99 65 04 28 06 16 70 92)
                                    (41 41 26 56 83 40 80 70 33)
                                    (41 48 72 33 47 32 37 16 94 29)
                                    (53 71 44 65 25 43 91 52 97 51 14)
                                    (70 11 33 28 77 73 17 78 39 68 17 57)
                                    (91 71 52 38 17 14 91 43 58 50 27 29 48)
                                    (63 66 04 68 89 53 67 30 73 16 69 87 40 31)
                                    (04 62 98 27 23 09 70 98 73 93 38 53 60 04 23))))
  (destructuring-bind (first . rest) (reverse trig)
    (car (reduce (lambda (path row)
                   (loop for (i i+1) on path by #'cdr
                         for ti in row
                         collect (+ ti (max i i+1))))
                 rest
                 :initial-value first))))


;;; Problem 19. Counting Sundays
;; How many Sunday fell on the first of the month during the twentieth
;; century (1 Jan 1901 to 31 Dec 2000)
;;

(deftype month () '(integer 1 12))
(deftype day   () '(integer 1 31))

(defstruct date
  (year  0 :type integer)
  (month 1 :type month)
  (day   1 :type day))

(defun-inline leap-year-p (date)
  "Test if DATE is leap year. "
  (let ((year (date-year date)))
    (and (modp year 4)
         (or (not (modp year 100))
             (modp year 400)))))

(defun days-of-month (date)
  "Return the number of days in DATE month. "
  ;;                       1  2  3  4  5  6  7  8  9  10 11 12
  (let ((day-of-month #(0 31 28 31 30 31 30 31 31 30 31 30 31)))
    (+ (aref day-of-month (date-month date))
       (if (and (= (date-month date) 2) (leap-year-p date)) 1 0))))

(defun next-day (date)
  "Return the day next DATE. "
  (declare (type date date))
  (let ((days  (days-of-month date))
        (day   (date-day   date))
        (month (date-month date))
        (year  (date-year  date)))
    (when (> (incf day) days)
      (setf day 1)
      (when (> (incf month) 12)
        (setf month 1)
        (incf year)))
    (make-date :year year :month month :day day)))

(defun date (year month day)
  "Make a date YEAR MONTH DAY. "
  (make-date :year year :month month :day day))

;; Sakamoto's methods
;; cite: https://en.wikipedia.org/wiki/Determination_of_the_day_of_the_week#Sakamoto's_methods
(defun week-of-day (date)
  "Return the week of DATE. "
  (let ((week #(:sunday :monday :tuesday :wednesday :thursday :friday :saturday))
        (dt   #(0 3 2 5 0 3 5 1 4 6 2 4)))
    (flet ((/* (a b) (truncate a b)))
      (let* ((m (date-month date))
             (y (if (< m 3)
                    (1- (date-year date))
                    (date-year date)))
             (d (date-day date)))
        (aref week (mod (+ y (/* y 4) (/* y -100) (/* y 400) (aref dt (1- m)) d) 7))))))

(defmethod print-object ((date date) stream)
  (format stream
          "~4,'0D-~2,'0D-~2,'0D ~A"
          (date-year  date)
          (date-month date)
          (date-day   date)
          (week-of-day date)))

(defun date= (date1 date2)
  "Test if DATE1 and DATE2 is same day. "
  (and (= (date-year  date1) (date-year  date2))
       (= (date-month date1) (date-month date2))
       (= (date-day   date1) (date-day   date2))))

(defun date< (date1 date2)
  "Test if DATE1 is earlier than DATE2. "
  (declare (type date date1 date2))
  (if (= (date-year date1) (date-year date2))
      (if (= (date-month date1) (date-month date2))
          (< (date-day date1) (date-day date2))
          (< (date-month date1) (date-month date2)))
      (< (date-year date1) (date-year date2))))

(defun date<= (date1 date2)
  "Test if DATE1 is eariler or equal to DATE2. "
  (declare (type date date1 date2))
  (or (date< date1 date2) (date= date1 date2)))

(defun problem19 (&key (start (date 1901 1 1)) (end (date 2000 12 31)) (day :sunday))
  "Count how many DAY fall on first month during START and END. "
  (loop for today = start then (next-day today)
        while (date<= today end)
        count (and (= (date-day today) 1) (eq (week-of-day today) day))))


;;; Problem 20. Factorial Digit Sum
;; n! means n * (n - 1) * ... * 3 * 2 * 1.
;;
;; For example, 10! = 10 * 9 * ... * 3 * 2 * 1 = 3628800,
;; and the sume of the digits in the number 10! is 3 + 6 + 2 + 8 + 8 + 0 + 0 = 27.
;;
;;
;; Find the sum of the digits in the number 100!.
;;

(defun factorial (n)
  "Return N!. "
  (loop with fact = 1
        for i from 1 upto n
        do (setf fact (* fact i))
        finally (return fact)))

(defun problem20 (&optional (n 100))
  "Return the sum of the digits of N!. "
  (sum (p-digits (factorial n))))


;;; Problem 21. Amicable Numbers
;; Let d(n) be defined as the sum of proper divisors of n (numbers less than
;; n which divide evenly into n). If d(a) = b and d(b) = a, where a != b,
;; then a and be are amicable pair and each of a and b are called amicable
;; numbers.
;;
;; For example, the proper divisors of 220 are 1, 2, 4, 5, 10, 11, 20,
;; 22, 44, 55 and 100; therefore d(220) = 284. The proper divisors of 284
;; are 1, 2, 4, 71 and 142; so d(284) = 220.
;;
;; Evaluate the sum of all the amicable numbers under 10000.
;;

(defun problem21 (&optional (max 10000))
  "Return the sum of all the amicable numbers under MAX. "
  (let ((d (make-array (1+ max)))
        (a ()))
    ;; calculate d(n) and store them to array `d'
    (loop for n from 1 below max do
      (setf (aref d n) (- (sum (divisors n)) n)))
    ;; search for the d(d(a)) = a
    (flet ((d (x) (if (or (< x 0) (> x max)) -1 (aref d x))))
      (loop for n from 1 below max do
        (when (and (= (d (d n)) n) (/= (d n) n))
          (pushnew (d n) a)
          (pushnew n     a))))
    (sum a)))


;;; Problem 22. Name Scores
;; Using names.txt, a 46K text file containing over five-thousand
;; first names, begin by sorting it into alphabetical order.
;; Then working out the alphabetical value for each name, multiply
;; this value by its alphabetical position in the list to obtain
;; a name score.
;;
;; For example, when the list is sorted into alphabetical order,
;; COLIN, which is worth 3 + 15 + 12 + 9 + 14 = 53, is the 938th
;; name in the list. So COLIN would obtain a score of 938 * 53 = 49714.
;;
;; What is the total of all the name scores in the file?
;;

(defun read-file (path &optional (eof-error-p t) eof-value)
  "Read file at PATH. "
  (with-open-file (stream path)
    (read stream eof-error-p eof-value)))

(defun problem22 ()
  (let ((scores (mapcar (lambda (name)
                          (loop for c across name
                                sum (- (char-code c) (char-code #\A) -1)))
                        (sort (read-file "./dat/0022_names.sexp") #'string<))))
    (loop for i from 1
          for score in scores
          sum (* i score))))


;;; Problem 23. Non-Abundant Sums
;; A perfect number is a number for which the sum of its proper divisors
;; is exactly equal to the number. For example, the sum of the proper divisors
;; of 28 would be 1 + 2 + 4 + 7 + 14 = 28, which means that 28 is a
;; perfect number.
;;
;; A number n is called deficient if the sum of its proper divisors is
;; less than n and it is called abundant if this sum exceeds n.
;;
;; As 12 is the smallest abundant number, 1 + 2 + 3 + 4 + 6 = 16, the
;; smallest number that can be written as the sum of two abundant numbers
;; is 24. By mathematical analysis, it can be shown that all integers
;; greater than 28123 can be written as the sum of two abundant numbers.
;; However, this upper limit cannot be reduced any further by analysis
;; even though it is known that the greatest number that cannot be expressed
;; as the sum of two abundant numbers is less than this limit.
;;
;; Find the sum of all the positive integers which cannot be written
;; as the sum of two abundant numbers.

(defun-cached (abundant-number-p :fallback :null) (n)
  "Test if N is abundant number. "
  (< n (- (sum (divisors n)) n)))

(defun sum-of-abundant-number-p (n)
  "Test if N can be splited as two abundant number. "
  (loop for i from (1- n) downto 1
        for j = (- n i)
        while (<= j i)
        if (and (abundant-number-p i)
                (abundant-number-p j))
          return t
        finally (return nil)))

(defun problem23 ()
  "Return the sum of all the positive integers which cannot be
written as two abundant numbers. "
  (let ((cache (make-array (1+ 28123))))
    (loop for i from 12 upto 28123
          do (setf (aref cache i) (abundant-number-p i)))
    (loop for n from 1 upto 28123
          if (not (sum-of-abundant-number-p n))
            sum n)))


;;; Problem 24. Lexicographic Permutations
;; A permutation is an ordered arrangement of objects.
;; For example, 3124 is one possible permutation of the digits
;; 1, 2, 3 and 4. If all of the permutations are listed numerically
;; or alphabetically, we call it lexicographic order.
;; The lexicographic permutations of 0, 1 and 2 are:
;;
;;   012 021 102 120 201 210
;;
;; What is the millionth lexicographic permutation of the digits
;;
;;   0, 1, 2, 3, 4, 5, 6, 7, 8 and 9
;;

;; The idea is Zipper data structure:
;;
;;     unfold  |   fold
;;               (1 2 3 4)
;;         (1)   (2 3 4)    ; move
;;       (2 1)   (3 4)      ; move
;;     (4 2 1)   (4)        ; move
;;             ^
;;      current position
;;

(defun insert-between-list (list elem)
  "Insert ELEM in LIST and return a new list of all the inserted new list.

Example:

    (insert-between-list '(1) 2)
    ;; => ((1 2) (2 1))
"
  (loop with folded = ()
        with unfold = list
        with collected = ()
        while unfold
        do (push (append (reverse folded) (list elem) unfold) collected)
        do (push (pop unfold) folded)
        finally (progn
                  (push (reverse (cons elem folded)) collected)
                  (return collected))))

;; Algorithm:
;; permutation-list(()) = '(())
;; permutation-list(elements = (first . rest))
;;  = insert-between(one of permutation-list(rest), first)
;;
;; for example:
;;
;; (trace permutation-list)
;;
;; 0: (EULER::PERMUTATION-LIST (0 1 2))
;;   1: (EULER::PERMUTATION-LIST (1 2))
;;     2: (EULER::PERMUTATION-LIST (2))
;;       3: (EULER::PERMUTATION-LIST NIL)
;;       3: permutation-list returned (nil)
;;     2: permutation-list returned ((2))
;;   1: permutation-list returned ((2 1) (1 2))
;; 0: permutation-list returned ((2 1 0) (2 0 1) (0 2 1) (1 2 0) (1 0 2) (0 1 2))
;;

(defun permutation-list (elements)
  "Return a list of permutated of ELEMENTS.

Example:

    (permutation-list (range-list 0 2))
    ;; => ((2 1 0) (2 0 1) (0 2 1) (1 2 0) (1 0 2) (0 1 2))

"
  (if (endp elements) '(())
      (apply #'append
             (mapcar (rcurry #'insert-between-list (car elements))
                     (permutation-list (cdr elements))))))

(defun list< (list1 list2)
  "Test if two LIST1 and LIST2 are in lexicographic order. "
  (if (endp list1) t
      (let ((e1 (car list1))
            (e2 (car list2)))
        (cond ((= e1 e2) (list< (cdr list1) (cdr list2)))
              ((< e1 e2) t)
              (t         nil)))))

(defun lexicographic-permutation-list (elements)
  "Return a lexicographic permutation list of ELEMENTS. "
  (sort (permutation-list elements) #'list<))

(defun problem24 ()
  "Return million-th lexicographic permutation. "
  (nth (1- +million+) (lexicographic-permutation-list (range-list 0 9))))


;;; Problem 25. 1000-digit Fibonacci Number
;; What is the index of the first term in the Fibonacci sequence
;; to contain 1000 digits.

(defun count-digits (n &optional (base 10))
  "This is equal to (length (digits n base)). "
  (1+ (truncate (log n base))))

(defun problem25 (&optional (digits 1000))
  "Return the first Fibonacci number contain DIGITS. "
  (loop with f1 = 1
        with f2 = 1
        for i from 2
        if (= (count-digits f2) digits)
          return i
        do (shiftf f1 f2 (+ f1 f2))))


;;; Problem 26. Reciprocal Cycles
;; A unit fraction contains 1 in the number. The decimal representation
;; of the unit fractions with denominators 2 to 10 are given:
;;
;;   1/2 = 0.5
;;   1/3 = 0.(3)
;;   1/4 = 0.25
;;   1/5 = 0.2
;;   1/6 = 0.1(6)
;;   1/7 = 0.(142857)
;;   1/8 = 0.125
;;   1/9 = 0.(1)
;;  1/10 = 0.1
;;
;; Where 0.1(6) means 0.166666..., and has a 1-digit recurring cycle.
;; It can be seen that 1/7 has a 6-digit recurring cycle.
;;
;; Find the value of d < 1000 for which 1/d contains the longest
;; recurring cycle in its decimal fraction part.
;;

(defun proper-fraction (rational)
  "Return values are proper fraction of RATIONAL, mixed number. "
  (let ((n (numerator   rational))
        (d (denominator rational)))
    (values (/ (mod n d) d) (* d (floor (/ n d))))))

;; if only contain 2 or 5, the RATIONAL is not infinite
;; loop decimal number

(defun infinite-loop-decimal-number-p (rational)
  "Test if RATIONAL is infinite loop decimal number. "
  (declare (type rational rational))
  (and (find-if (lambda (fact-order)
                  (destructuring-bind (fact . order) fact-order
                    (declare (ignore order))
                    (and (/= fact 2) (/= fact 5))))
                (factors (denominator rational)))
       t))

;; If remainder of long division starts to repeat,
;; the dicimal would start to repeat.

(defun decimal-recurring-cycle (rational)
  "Return the decimal recurring cycle list of RATIONAL. "
  (declare (type rational rational))
  (when (infinite-loop-decimal-number-p rational)
    (let* ((rational (proper-fraction rational))
           (n (numerator   rational))
           (d (denominator rational)))
      (loop for num = (mod n d) then (mod (* num 10) d)
            for idx from 0
            for digit     = (floor (/ (* num 10) d))
            for remainder = (mod num d)

            ;; remainder is ((nth-division-remainder . nth) ...)
            ;; which is used to test if repeating
            for repeat    = (find remainder remainders :key #'car)
            while (not repeat)
            collect digit into cycle
            collect (cons remainder idx) into remainders
            finally (return (values (nthcdr (cdr repeat) cycle)
                                    (subseq cycle 0 (cdr repeat))))))))

(defun problem26 (&optional (max 1000))
  "Return the longest decimal part. "
  (loop with dmax = 0
        with lmax = 0
        for d from 1 below max
        for l = (length (decimal-recurring-cycle (/ 1 d)))
        if (> l lmax)
          do (setf lmax l
                   dmax d)
        finally (return dmax)))


;;; Problem 27. Quadratic Primes
;; Euler discovered the remarkable quadratic formula:
;;
;;     n^2 + n + 41
;;
;; It turns out that the formula will produce 40 primes for the
;; consecutive integer values 0 <= n <= 39. However, when n = 40,
;; 40^2 + 40 + 41 = 40 * (40 + 1) + 41 is divisible by 41, and
;; certainly when n = 41, 41^2 + 41 + 41 is clearly divisible by 41.
;;
;; The incredible formula n^2 - 79 * n + 1601 was discovered,
;; which produces 80 primes for the consecutive values 0 <= n <= 79.
;; The product of the coefficients, -79 and 1601, is -126479.
;;
;; Considering quadratics of the form:
;;
;;     n^2 + a * n + b, where |a| < 1000 and |b| <= 1000
;;
;;     where |n| is the modulus/absolute value of n,
;;     e.g. |11| = 11 and |-4| = 4
;;
;; Find the product of the coefficients, a and b, for the quadratic
;; expression that produces the maximum number of primes for
;; consecutive values of n, starting with n = 0.
;;

(defun quadratic-formula-prime-ability-count (a b)
  "Count the max n of n^2 + a * n + b that make it as a prime.

Example:

    (quadratic-formula-prime-ability-count   1   41) ; => 40
    (quadratic-formula-prime-ability-count -79 1601) ; => 80
"
  (loop for n from 0
        for primep = (primep (abs (+ (square n) (* a n) b)))
        while primep
        count primep))

(defun problem27 (&optional (amax (1- 1000)) (bmax 1000))
  "Find the product of the coefficients of the max
quadratic formula prime count. "
  (loop with max-a = 0
        with max-b = 0
        with max   = 0
        for a from (- amax) upto amax
        do (loop for b from (- bmax) upto bmax
                 for cnt = (quadratic-formula-prime-ability-count a b)
                 if (> cnt max)
                   do (setf max   cnt
                            max-a a
                            max-b b))
        finally (return (* max-a max-b))))


;;; Problem 28. Number Spiral Diagonals
;; Starting with the number 1 and moving to the right in a clockwise
;; direction a 5 by 5 spiral is formed as follows:
;;
;;    21 22 23 24 25
;;    20  7  8  9 10
;;    19  6  1  2 11
;;    18  5  4  3 12
;;    17 16 15 14 13
;;
;; It can be verified that the sum of the numbers on the diagonals
;; is 101.
;;
;; What is the sum of the numbers on the diagonals in a 1001 by 1001
;; spiral formed in the same way?
;;

;; width of nth layer: 1, 3, 5, ...
;; start of nth layer: end of n-1th layer + width of nth layer + 1

(defun problem28 (&optional (size 1001))
  "Return the sum of the diagonals. "
  (loop with sum = 1
        with num = 1
        for layer from 2
        for width from 3 upto size by 2
        ;; calculate start of nth layer, sum it
        do (incf sum (incf num (1+ (- width 2))))
        do (dotimes (i 3) (incf sum (incf num (1- width))))
        finally (return sum)))


;;; Problem 29. Distinct Powers
;; Consider all integer combinations of a^b for 2 <= a <= 5 and 2 <= b <= 5:
;;
;;    2^2 = 4,     2^3 = 8,    2^4 = 16,    2^5 = 32
;;    3^2 = 9,     3^3 = 27,   3^4 = 81,    3^5 = 243
;;    4^2 = 16,    4^3 = 64,   4^4 = 256,   4^5 = 1024
;;    5^2 = 25,    5^3 = 125,  5^4 = 625,   5^5 = 3125
;;
;; If they are then placed in numerical order, with any repeats
;; removed, we get the following sequence of 15 distinct terms:
;;
;;    4, 8, 9, 16, 25, 27, 32, 64, 81, 125, 243, 256, 625, 1024, 3125
;;
;; How many distinct terms are in the sequence generated by a^b for
;; 2 <= a <= 100 and 2 <= b <= 100?
;;

(defun problem29 (&optional (amax 100) (bmax 100))
  "Return terms of a^b. "
  (loop for a from 2 upto amax
        collect (loop for b from 2 upto bmax
                      collect (expt a b))
          into terms
        finally (return (length (reduce #'union terms)))))


;;; Problem 30. Digit Fifth Powers
;; Surprisingly there are only three numbers that can be written as the sum
;; of fourth powers of their digits:
;;
;;    1634 = 1^4 + 6^4 + 3^4 + 4^4
;;    8208 = 8^4 + 2^4 + 0^4 + 8^4
;;    9474 = 9^4 + 4^4 + 7^4 + 4^4
;;
;; As 1 = 1^4 is not a sum it is not included.
;;
;; The sum of these numbers is 1634 + 8208 + 9474 = 19316.
;;
;; Find the sum of all the numbers that can be written as the
;; sum of fifth powers of their digits.
;;

;; Notice that 9^5 * 6 < 111111 gives the upper limit of the
;; number that could be written as the sum of powers of digits

(defun solve-count-digits-n*9^k=n (k)
  "Solve the equation of: (count-digits 9^k * n) <= n. "
  (loop with 9^k = (expt 9 k)
        for sum from (+ 9^k 9^k) by 9^k
        for n from 3
        if (<= (count-digits sum) n)
          return n))

(defun problem30 (&optional (exp 5))
  "Return the sum of numbers that can be written as sum of EXP powers of its digits. "
  (loop for n from 2 below (* (solve-count-digits-n*9^k=n exp) (expt 9 exp))
        if (= n (sum (mapcar (lambda (d) (expt d exp)) (p-digits n))))
          sum n))


;;; Problem 31. Coin Sums
;; In the United Kingdom the currency is made up of pound (£) and pence (p).
;; There are eight coins in general circulation:
;;
;;    1p, 2p, 5p, 10p, 20p, 50p, £1 (100p), and £2 (200p)
;;
;; It is possible to make £2 in the following way:
;;
;;    1 * £1  + 1 * 50p + 2 * 20p + 1 * 5p + 1 * 2p + 3 * 1p
;;
;; How many different ways can £2 be made using any number of coins?
;;

(ql:quickload :sycamore)

;; The tree is used for faster insert

(defun coin-split (total &optional (coins (list 1 2 5 10 20 50 100 200)))
  "Count how many ways to split TOTAL coin with COINS. "
  (let ((coins (sort coins #'<))
        (len (length coins)))
    (flet ((compare (pat1 pat2)
             (loop for id1 from 0 below len
                   for id2 from 0 below len
                   if (< (aref pat1 id1) (aref pat2 id2))
                     return -1
                   if (> (aref pat1 id2) (aref pat2 id2))
                     return  1
                   finally (return 0)))
           (inc-pattern (pat idx)
             (let ((pat (if (arrayp pat)
                            (make-array len :initial-contents pat)
                            (make-array len :initial-element  pat))))
               (incf (aref pat idx))
               pat)))
      (let ((cache (make-array total)))
        (loop for tol from 1 upto total do
          (loop with patterns = (sycamore:tree-set #'compare)
                for idx from 0
                for coin in coins
                if (= coin tol)
                  do (setf patterns (sycamore:tree-set-insert patterns (inc-pattern 0 idx)))
                if (< coin tol)
                  do (sycamore:map-tree-set
                      nil
                      (lambda (pat)
                        (setf patterns (sycamore:tree-set-insert patterns (inc-pattern pat idx))))
                      (aref cache (1- (- tol coin))))
                finally (setf (aref cache (1- tol)) patterns))
              do (print (cons tol (sycamore:tree-set-count (aref cache (1- tol)))))
              finally (return (aref cache (1- total))))))))

(defun problem31 (&optional (total 200))
  "Return how many different ways can 200 be splited. "
  (length (coin-split total)))


;;; Problem 32. Pandigital Products
;; We shall say that an n-digit number is pandigital if it makes use of all
;; the digits 1 to n exactly once; for example, the 5-digit number, 15234
;; is 1 through 5 pandigital.
;;
;; The product 7254 is unusual, as the identity, 39 * 186 = 7254, containing
;; multiplicand, multiplier, and product is 1 through 9 pandigital.
;;
;; Find the sum of all products whose multiplicand / multiplier / product
;; identity can be written as a 1 through 9 pandigital.
;;
;; HINT: Some products can be obtained in more than one way so be sure to only
;; include it once in your sum.
;;

(defun split-list-map (func list n)
  "Split LIST into N parts (not empty) and apply FUNC on splited.

Example:

    (split-list-map func '(1 2 3) 2)
    ;; => (func '(1) '(2 3))
    ;; => (func '(1 2) '(3))
"
  (declare (type function func)
           (type list list)
           (type (integer 1) n))
  (labels ((iter (list n prev)
             (if (= n 1)
                 (apply func (reverse (cons list prev)))
                 (loop for (elem . rest) on list
                       collect elem into split
                       while (not (endp rest))
                       do (iter rest (1- n) (cons split prev))))))
    (iter list n ())))

(defun problem32 (&optional (n 9))
  "Return the sum of all products. "
  (let ((products ()))
    (dolist (digits (permutation-list (range-list 1 n)) (sum products))
      (split-list-map (lambda (a b prod)
                        (let ((prod (int<-p-digits prod)))
                          (when (= (* (int<-p-digits a) (int<-p-digits b)) prod)
                            (pushnew prod products))))
                      digits
                      3))))


;;; Problem 33. Digit Cancelling Fractions
;; The fraction 49/98 is a curious fraction, as an inexperienced mathematician
;; in attempting to simplify it may incorrectly believe that 49/98 = 4/8,
;; which is correct, is obtained by cancelling the 9s.
;;
;; We shall consider fractions like, 30/50 = 3/5, to be trivial examples.
;;
;; These are exactly four non-trivial examples of this type of fraction,
;; less than one in value, and containing two digits in the numerator and
;; denominator.
;;
;; If the product of these four fractions is given in its lowest common
;; terms, find the value of the denominator.
;;

(defun list-xor (list1 list2 &key (test #'eql))
  "Return values are XORed LIST1 and LIST2 by TEST.

Example:

    (list-xor '(1 2 3) '(2 3 4))
    ;; => (1), (4)
"
  (flet ((find* (list) (lambda (elem) (find elem list :test test))))
    (values (remove-if (find* list2) list1)
            (remove-if (find* list1) list2))))

(defun problem33 ()
  "Return the product of four fractions denominator. "
  (let ((fractions ()))
    (loop for d from 99 downto 12
          for d-digits = (p-digits d)
          do (loop for n from (1- d) downto 11
                   for n-digits = (p-digits n)
                   if (not (and (modp n 10) (modp d 10)))
                     do (multiple-value-bind (nn dd) (list-xor n-digits d-digits)
                          (let ((nn (int<-p-digits nn))
                                (dd (int<-p-digits dd)))
                            (when (and (not (zerop dd))
                                       (/= d dd) (/= n nn)
                                       (= (/ nn dd) (/ n d)))
                              (pushnew (/ n d) fractions)))))
          finally (return (prod fractions)))))


;;; Problem 34. Digit Factorials
;; 145 is a curious number, as 1! + 4! + 5! = 1 + 24 + 120 = 145.
;;
;; Find the sum of all numbers which are equal to the sum of the
;; factorial of their digits.
;;
;; Note: As 1! = 1 and 2! = 2 are not sums they are not included.
;;

;; Notice that 999999999 > 7 * 9! = 2540160.

(defun problem34 ()
  "Return the sum of all numbers which are equal to the sum of
the factorial of their digits. "
  (loop for i from 10 upto (* 7 (factorial 9))
        if (= i (sum (mapcar #'factorial (p-digits i))))
          sum i))


;;; Problem 35. Circular Primes
;; The number, 197, is called a circular prime because all rotations of
;; the digits: 197, 971 and 719, are themselves prime.
;;
;; There are thirteen such primes below 100:
;; 2, 3, 5, 7, 11, 13, 17, 31, 37, 71, 73, 79, and 97
;;
;; How many circular primes are there below one million?
;;

(defun rotate-list (list &optional (n 1))
  "Return rotated LIST by N. "
  (append (subseq list n) (subseq list 0 n)))

(defun circular-prime-p (n)
  "Test if N is circular prime.
Return values are boolean, rotated primes list. "
  (loop with n-digits = (p-digits n)
        for digits = n-digits then (rotate-list digits)
        for num = (int<-p-digits digits)
        repeat (length n-digits)
        if (primep num)
          collect num into primes
        else
          return (values nil nil)
        finally (return (values t primes))))

(defun problem35 (&optional (max +million+))
  "Count circular primes below MAX. "
  (loop with cache = (sycamore:tree-set (lambda (a b)
                                          (cond ((< a b) -1)
                                                ((> a b)  1)
                                                (t        0))))
        for n from 2 below max
        if (not (sycamore:tree-set-member-p cache n))
          do (multiple-value-bind (- primes) (circular-prime-p n)
               (dolist (prime primes)
                 (setf cache (sycamore:tree-set-insert cache prime))))
        finally (return (sycamore:tree-set-count cache))))


;;; Problem 36. Double-base Palindromes
;; The decimal number, 585 = #b1001001001 (binary), is palindromic
;; in both bases.
;;
;; Find the sum of all numbers, less than one million, which are
;; palindromic in base 10 and base 2.
;;

(defun problem36 (&optional (max +million+) (base1 10) (base2 2))
  "Return the dual palindromic in BASE1 and BASE2 below MAX. "
  (loop for n from 1 below max
        if (and (palindromep n base1)
                (palindromep n base2))
          sum n))


;;; Problem 37. Truncatable Primes
;; The number 3797 has an interesting property. Being prime itself,
;; it is possible to continuously remove digits from left to right,
;; and remain prime at each stage: 3797, 797, 97, and 7. Similarly
;; we can work from right to left: 3797, 379, 37, and 3.
;;
;; Find the sum of the only eleven primes that are both truncatable
;; from left to right and right to left.
;;
;; Note: 2, 3, 5, and 7 are not considered to be truncatable primes.

(defun truncatable-prime-p (prime &optional (base 10))
  "Test if PRIME is a truncatable prime.

Note 2, 3, 5, 7 are not considered to be truncatable primes. "
  (and (> prime 10)
       (loop for digits on (p-digits prime base)
             if (not (primep (int<-p-digits digits)))
               return nil
             finally (return t))
       (loop for p = (p-shift prime base) then (p-shift p base)
             until (zerop p)
             if (not (primep p))
               return nil
             finally (return t))))

(defun problem37 ()
  "Find the sum of the only eleven primes that are truncatable primes. "
  (loop for p from 13
        if (truncatable-prime-p p)
          collect p into primes
        while (/= (length primes) 11)
        finally (return (sum (print primes)))))


;;; Problem 38. Pandigital Multiples
;; Take the number 192 and multiply it by each of 1, 2, and 3:
;;
;;    192 * 1 = 192
;;    192 * 2 = 384
;;    192 * 3 = 576
;;
;; By concatenating each product we get the 1 to 9 pandigital,
;; 192384576. We will call 192384576 the concatenated product
;; of 192 and (1, 2, 3).
;;
;; The same can be achieved by starting with 9 and multiplying
;; by 1, 2, 3, 4, and 5, giving the pandigital, 918273645,
;; which is the concatenated product of 9 and (1, 2, 3, 4, 5).
;;
;; What is the largest 1 to 9 pandigital 9-digit number that
;; can be formed as the concatenated product of an integer with
;; (1, 2, ..., n) where n > 1?
;;

(defun concatenate-product (n multipliers &optional (base 10))
  "Return the concatenating product of N and MULTIPLIERS.

Example:

    (concatenate-product 192 '(1 2 3))
    ;; => 192384576
"
  (int<-p-digits (apply #'concatenate 'list
                        (mapcar (lambda (mul) (p-digits (* n mul) base)) multipliers))
                 base))

(defun have-digits-p (num digits &key (base 10) (strictp t) (uniquep t))
  "Test if NUM has DIGITS and having them only. "
  (let ((cache (make-array base :initial-element :not-used)))
    (loop for digit in digits do (setf (aref cache digit) nil))
    (loop for digit in (p-digits num base)
          do (cond ((eq (aref cache digit) :not-used)
                    (when strictp (return nil)))
                   ((eq (aref cache digit) t)
                    (when uniquep (return nil)))
                   ((eq (aref cache digit) nil)
                    (setf (aref cache digit) t)))
          finally (return (if strictp
                              ;; check all digit is used
                              (loop for digit in digits
                                    if (not (aref cache digit))
                                      return nil
                                    finally (return t))
                              t)))))

(defun problem38 ()
  "Return the largest pandigital 9-digit number that can be formed as the
product of an integer with (1, ..., n). "
  (loop with max = 0
        for n from 2 upto 9
        for ns = (range-list 1 n)
        do (loop for i from 1
                 for prod = (concatenate-product i ns)
                 while (<= prod 987654321)
                 if (and (> prod max) (have-digits-p prod (range-list 1 9)))
                   do (setf max prod))
        finally (return max)))


;;; Problem 39. Integer Right Triangles
;; If p is the perimeter of a right angle triangle with integral length
;; sides, {a, b, c}, there are exactly three solutions for p = 120.
;;
;;   {20, 48, 52}, {24, 45, 51}, {30, 40, 50}
;;
;; For which value of p <= 1000, is the number of solutions maximised?
;;
;;

(defun right-angle-triangle-p (a b c)
  "Test if A, B, C is a right angle triangle. "
  (let* ((max (max a b c))
         (min (min a b c))
         (mid (- (+ a b c) (+ min max))))
    (= (+ (square min) (square mid)) (square max))))

(defun split-number-map (func num n)
  "Split NUM into N parts and apply FUNC on splited.

Example:

    (split-number-map func 3 2)
    ;; => (func 2 1)
    ;; => (func 1 2)
"
  (declare (type function func)
           (type number num)
           (type (integer 1) n))
  (labels ((iter (num n prev)
             (if (= n 1)
                 (apply func (reverse (cons num prev)))
                 (loop with n-1 = (1- n)
                       for elem from (- num n-1) downto n-1
                       do (iter (- num elem) n-1 (cons elem prev))))))
    (iter num n ())))

(defun count-right-angle-triangle-splittable (p)
  "Count for patterns {a, b, c} is right angle triangle, and a + b + c = p. "
  (let ((count 0))
    (split-number-map (lambda (a b c)
                        (when (and (<= a b c) (right-angle-triangle-p a b c))
                          (incf count)))
                      p 3)
    count))

(defun problem39 (&optional (max 1000))
  "Return the max of count right angle triangle splittable p < MAX. "
  (loop with max-cnt = 0
        with max-p   = 0
        for p from 12 below max
        for cnt = (count-right-angle-triangle-splittable p)
        if (> cnt max-cnt)
          do (setf max-cnt cnt
                   max-p   p)
        finally (return max-p)))


;;; Problem 40. Champernowne's Constant
;; An irrational decimal fraction is created by concatenating the positive
;; integers:
;;
;;    0.123456789101112131415161718192021...
;;                 ^
;;                12th
;;
;; It can be seen that the 12th digit of the fractional part is 1.
;;
;; If d(n) represents the nth digit of the fractional part, find the value
;; of the following expression.
;;
;;    d1 * d10 * d100 * d1000 * d10000 * d100000 * d1000000
;;

(defun problem40 (&optional (indexs (mapcar (curry #'expt 10) (range-list 1 6))))
  "Return product of d(indexs). "
  (loop with idxs = (sort indexs #'<)
        with nth = 1
        with prod = 1
        with current = (pop idxs)
        for num from 1
        do (loop for di in (p-digits num)
                 if (= nth current)
                   do (setf prod    (* di prod)
                            current (pop idxs))
                 do (incf nth)
                 while current)
        while current
        finally (return prod)))


;;; Problem 41. Pandigital Prime
;; We shall say that an n-digit number is pandigitial if it makes use
;; of all the digits 1 to n exactly once. For example, 2143 is a
;; 4-digit pandigital and is also prime.
;;
;; What is the largest n-digit pandigital prime that exists?
;;

(defun pandigitalp (n &optional (base 10))
  "Test if N is pandigital number. "
  (let ((digits (count-digits n base)))
    (when (< digits base)
      (have-digits-p n (range-list 1 digits)
                     :base base :uniquep t :strictp t))))

(defun problem41 ()
  "Find the largest n-digit pandigital prime. "
  (loop for p from 2143 below 987654321 by 2
        if (and (pandigitalp p) (primep p))
          maximize (print p)))

(defun problem41-other-way ()
  "Find the largest n-digit pandigital prime. "
  (loop for n from 9 downto 1
        for max = (loop for p-digits in (permutation-list (range-list 1 n))
                        for p = (int<-p-digits p-digits)
                        if (primep p)
                          maximize p)
        while (zerop max)
        finally (return max)))


;;; Problem 42. Coded Triangle Numbers
;; The nth term of the sequence of triangle numbers is given by
;; t(n) = n * (n + 1) / 2; so the first ten triangle numbers are:
;;
;;    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...
;;
;; By converting each letter in a word to a number corresponding to its
;; alphabetical position and adding these values we form a word value.
;; For example, the word value for SKY is 19 + 11 + 25 = 55 = t(10).
;; If the word value is a triangle number then we shall call the word
;; a triangle word.
;;
;; Using words.txt containing nearly two-thousand common English
;; words, how many are triangle words?
;;

(defun triangle-number (n)
  "Return triangle number n * (n + 1) / 2. "
  (declare (type integer n))
  (/ (* n (1+ n)) 2))

;; solve equation:
;; x ( x + 1 ) = 2 n
;; => (sqrt(1 + 8 * n) - 1) / 2

(defun triangle-number-p (n)
  "Test if N is triangle number. "
  (let* ((square (1+ (* 8 n)))
         (sqrt   (truncate (sqrt square))))
    (and (= square (square sqrt))
         (evenp (1- sqrt)))))

(defun triangle-word-p (word)
  "Test if WORD is triangle word. "
  (triangle-number-p
   (sum (map 'list (lambda (c) (- (char-code c) (char-code #\A) -1)) word))))

(defun problem42 ()
  "Count triangle words. "
  (loop for word in (read-file "./dat/0042_words.sexp")
        count (triangle-word-p word)))


;;; Problem 43. Sub-string Divisibility
;; The number, 1406357289, is a 0 to 9 pandigital number because it is
;; made up of each of the digits 0 to 9 in some order, but it also has
;; a rather interesting sub-string divisibility property.
;;
;; Let d(1) be the 1st digit, d(2) be the 2nd digit, and so on. In this way,
;; we note the following:
;;
;;  + d2 * d3 * d4  = 406 is divisible by 2
;;  + d3 * d4 * d5  = 063 is divisible by 3
;;  + d4 * d5 * d6  = 635 is divisible by 5
;;  + d5 * d6 * d7  = 357 is divisible by 7
;;  + d6 * d7 * d8  = 572 is divisible by 11
;;  + d7 * d8 * d9  = 728 is divisible by 13
;;  + d8 * d9 * d10 = 289 is divisible by 17
;;
;; Find the sum of all 0 to 9 pandigital numbers with this property.
;;

(defun 2+ (x)
  "Return x + 2. "
  (+ 2 x))

(defun n-digit-prime-dividable-p (n digits &optional (base 10))
  "Test if subsequence of N size of DIGITS can be divided by nth prime. "
  (let ((i      0)
        (digits (if (listp digits)
                    digits
                    (p-digits digits base))))
    (windowed-mapcar
     (lambda (&rest n-di)
       (unless (modp (int<-p-digits n-di base) (nth-prime (incf i)))
         (return-from n-digit-prime-dividable-p nil)))
     n digits)
    t))

(defun problem43 ()
  "Return the sum of all 0 to 9 pandigital numbers that can divide. "
  (loop for (d1 . digits) in (permutation-list (range-list 0 9))
        if (and (not (zerop d1)) ; 0********* should be ignored
                (n-digit-prime-dividable-p 3 digits))
          sum (int<-p-digits (cons d1 digits))))


;;; Problem 44. Pentagon Numbers
;; Pentagonal numbers are generated by the formula, P(n) = n * (3 * n - 1) / 2.
;; The first ten pentagonal numbers are:
;;
;;    1, 5, 12, 22, 35, 51, 70, 92, 117, 145, ...
;;
;; It can be seen that P(4) + P(7) = 22 + 70 = 92 = P(8).
;; However, their differnce, 70 - 22 = 48, is not pentagonal.
;;
;; Find the pair of pentagonal numbers, P(j) and P(k), for which their
;; sum and difference are pentagonal and D = |P(k) - P(j)| is minimised;
;; what is the value of D?
;;

(defun pentagonal-number (n)
  "Return P(n) = n * (3 * n - 1) / 2. "
  (/ (* n (- (* 3 n) 1)) 2))

;; P(i) = n => i = (1 + sqrt(1 + 24 * k)) / 6

(defun integer-square-p (n)
  "Test if N is m^2 where m is integer.
Return values are boolean, the sqrt of N (if t). "
  (if (and (integerp n) (>= n 0))
      (let ((sqrt (isqrt n)))
        (if (= (square sqrt) n)
            (values t   sqrt)
            (values nil nil)))
      (values nil nil)))

(defun pentagonal-number-p (n)
  "Test if N is pentagonal number. "
  (multiple-value-bind (sqrtp sqrt)
      (integer-square-p (1+ (* 24 n)))
    (if (and sqrtp (modp (1+ sqrt) 6))
        (values t   (/ (1+ sqrt) 6))
        (values nil nil))))

;; it is equal to searching:
;; Pi, Pj, Pk, Pl as pentagonal numbers

(defun problem44 ()
  "Find the minimal D|P(k) - P(j)| is pentagonal. "
  (let ((cache (make-hash-table)))
    (flet ((pentagonal (n)
             (or (gethash n cache)
                 (setf (gethash n cache) (pentagonal-number n)))))
      (loop for sumi from 4
            for sum  = (pentagonal sumi)
            do (loop for loweri from 1
                     for lower = (pentagonal loweri)
                     for upper = (- sum lower)
                     for diff  = (- upper lower)
                     while (< lower upper)
                     if (and (pentagonal-number-p upper)
                             (pentagonal-number-p diff))
                       do (return-from problem44 diff))))))


;;; Problem 45. Triangular, Pentagonal, and Hexagonal
;; Triangle, pentagonal, and hexagonal numbers are generated by the
;; following formulae:
;;
;; Triangle   T(n) = n * (n + 1) / 2
;; Pentagonal P(n) = n * (3 * n - 1) / 2
;; Hexagonal  H(n) = n * (2 * n - 1)
;;
;; It can be verified that T(285) = P(165) = H(143) = 40755
;;
;; Find the next triangle number that is also pentagonal and hexagonal.
;;

(defun hexagonal-number (n)
  "Return hexagonal number n * (2 * n - 1). "
  (* n (1- (* 2 n))))

;; (1 + sqrt(1 + 8 * n)) / 4

(defun hexagonal-number-p (n)
  "Test if N is hexagonal number. "
  (multiple-value-bind (sqrtp sqrt)
      (integer-square-p (1+ (* 8 n)))
    (if (and sqrtp (modp (1+ sqrt) 4))
        (values t   (/ (1+ sqrt) 4))
        (values nil nil))))

(defun problem45 ()
  (loop for i from (1+ 285)
        for ti = (triangle-number i)
        if (and (pentagonal-number-p ti)
                (hexagonal-number-p  ti))
          return ti))


;;; Problem 46. Goldbach's Other Conjecture
;; It was proposed by Christian Goldbach that every odd composite number
;; can be written as the sum of a prime and twice a square.
;;
;;    9 =  7 + 2 * 1^2
;;   15 =  7 + 2 * 2^2
;;   21 =  3 + 2 * 3^2
;;   25 =  7 + 2 * 3^2
;;   27 = 19 + 2 * 2^2
;;   33 = 31 + 2 * 1^2
;;
;; It turns out that the conjecture was false.
;;
;; What is the smallest odd composite that cannot be written as the sum
;; of a prime and twice a square?
;;

(defun splitable-as-p-2*n^2-p (n)
  "Split N as p + 2 * n^2.
Return boolean, p, n. "
  (loop for i from 0
        for p = 1 then (nth-prime i)
        for 2n^2 = (- n p)
        while (>= 2n^2 0)
        if (and (evenp 2n^2) (integer-square-p (/ 2n^2 2)))
          return (values t p (truncate (sqrt (/ 2n^2 2))))
        finally (return (values nil nil nil))))

(defun problem46 ()
  "Return the smallest odd composite cannot split. "
  (loop for i from 1 by 2
        while (splitable-as-p-2*n^2-p i)
        finally (return i)))


;;; Problem 47. Distinct Primes Factors
;; The first two consecutive numbers to have two distinct prime factors are:
;;
;;     14 = 2 * 7
;;     15 = 3 * 5
;;
;; The first three consecutive numbers to have three distinct prime factors
;; are:
;;
;;     644 = 2^2 * 7 * 23
;;     645 = 3   * 5 * 43
;;     646 = 2   * 17 * 19
;;
;; Find the first four consecutive integers to have four distinct prime
;; factors each. What is the first of these numbers?
;;

(defun problem47 (&optional (n 4))
  "Find the first four consecutive integers. "
  (loop for i from (prod (mapcar #'nth-prime (range-list 1 n)))
        if (and-repeat (j n) (= (length (factors (+ i j))) n))
          return i))


;;; Problem 48. Self Powers
;; The series, 1^1 + 2^2 + 3^3 + ... + 10^10 = 10405071317.
;;
;; Find the last ten digits of the series, 1^1 + 2^2 + 3^3 + ... + 1000^1000.
;;

(defun self-power (x)
  "Return x^x. "
  (expt x x))

(defun problem48 ()
  "Find the last ten digits of the series. "
  (int<-p-digits (last (p-digits (sum (mapcar #'self-power (range-list 1 1000)))) 10)))


;;; Problem 49. Prime Permutations
;; The arithmetic sequence, 1487, 4817, 8147, in which each of the terms
;; increases by 3330, is unusual in two ways: (i) each of the three terms
;; are prime, and, (ii) each of the 4-digit numbers are permutations of
;; one another.
;;
;; There are no arithmetic sequences made up of three 1-, 2-, or 3-digit
;; primes, exhibiting this property, but there is one other 4-digit
;; increasing sequence.
;;
;; What 12-digit number do you form by concatenating the three terms
;; in this sequence?
;;

(defun n-pick-list (set n)
  "Return a list of element as N pick from set.

Example:

    (n-pick-list '(1 2 3) 2)
    ;; => ((1 2) (1 3) (2 3))
"
  (declare (type list set)
           (type (integer 0) n))
  (if (= n 0) '(())
      (apply #'append
             (loop for (elem . rest) on set
                   collect (mapcar (curry #'cons elem)
                                   (n-pick-list rest (1- n)))))))

(defun n-digit-prime (n &optional (base 10))
  "Return prime number with N digits. "
  (loop for i from 1
        for p = (nth-prime i)
        if (>= (count-digits p base) n)
          return (values p i)))

(defun nearest-prime (x &optional (sticky :left))
  "Find the nearest prime number to N. "
  (declare (type (real 0) x)
           (type (member :left :nearest :right) sticky))
  (loop for n from 1
        for pn   = (nth-prime n)
        for pn+1 = (nth-prime (1+ n))
        if (<= pn x pn+1)
          return (ecase sticky
                   (:left
                    (values pn n))
                   (:nearest
                    (if (< (- x pn) (- pn+1 x))
                        (values pn   n)
                        (values pn+1 (1+ n))))
                   (:right
                    (values pn+1 (1+ n))))))

;; Note: the expression of the problem is a little ambigiuous.
;; Here's my version:
;;
;; Definition: a sequence a(n, b) = 1487, 4817, 8147, ... = 3330 * n + b
;;
;; Find the b that:
;; 1. make all a(n, b) is prime, if (a(n, b) is 4-digit
;; 2. permutation(p-digits(a(n, b))) should equal to a(n', b)
;;    a.k.a. digits of a(n, b) should equal to a(n', b)
;;

(defun count-p-digits (n &optional (base 10))
  "Return an array of BASE size for each digits of N. "
  (let ((ad (make-array base :initial-element 0 :element-type 'unsigned-byte)))
    (dolist (d (p-digits n base) ad) (incf (aref ad d)))))

(defun array= (arr1 arr2)
  "Test if two array ARR1 and ARR2 is equal. "
  (and (= (length arr1) (length arr2))
       (and-repeat (i (length arr1))
         (= (aref arr1 i) (aref arr2 i)))))

(defun p-digits-permutate-p (a b &optional (base 10))
  "Test if A and B is permutable digits. "
  (array= (count-p-digits a base) (count-p-digits b base)))

(defun problem49 ()
  "Return n digits. "
  (multiple-value-bind (p0 i0) (nearest-prime 1000 :right)
    (loop for i from i0
          for p  = p0 then (nth-prime i)
          for ps = (loop for q from (+ p 3330) below 9999 by 3330
                         if (and (primep q) (p-digits-permutate-p p q))
                           collect q)
          if (= (length ps) 2)
            collect (int<-p-digits (cons p ps) 10000)
          while (< p (- 9999 (* 2 3330))))))


;;; Problem 50. Consecutive Prime Sum
;; The prime 41, can be written as the sum of six consecutive primes:
;;
;;    41 = 2 + 3 + 5 + 7 + 11 + 13.
;;
;; This is the longest sum of consecutive primes that adds to a prime
;; below one-hundred.
;;
;; The longest sum of consecutive primes below one-thousand that adds
;; to a prime, contains 21 terms, and is equal to 953.
;;
;; Which prime, below one-million, can be written as the sum of the
;; most consecutive primes?
;;

(defun problem50 (&optional (max +million+))
  "Return the prime that can be written as sum of the consecutive primes. "
  (loop for lefts on (loop with sum = 0
                           for i from 1
                           for p = (nth-prime i)
                           while (< (+ sum p) max)
                           do (incf sum p)
                           collect p)
        maximize (loop with stfel = (reverse lefts)
                       for primes on stfel
                       for sum = (sum primes)
                       if (primep sum)
                         return sum
                       finally (return 0))))


;;; Problem 51. Prime Digit Replacements
;; By replacing the 1st digit of the 2-digit number *3, it turns out
;; that six of the nine possible values: 13, 23, 43, 53, 73 and 83,
;; are all prime.
;;
;; By replacing the 3rd and 4th digits of 56**3 with the same digit,
;; this 5-digit number is the first example having seven primes among
;; the ten generated numbers, yielding the family: 56003, 56113,
;; 56333, 56443, 56663, 56773, and 56993. Consequently 56003, being
;; the first member of this family, is the smallest prime with this
;; property.
;;
;; Find the smallest prime which, by replacing part of the number
;; (not necessarily adjacent digits) with the same digit, is part
;; of an eight prime value family.
;;

(defun p-digit-mask (n i &optional (base 10))
  "Mask number N at I (lower to higher) digits.

Example:

    (p-digit-mask 123 1) ; => 103
"
  (declare (type (integer 0) n i base))
  (let* ((cut1 (expt base i))
         (cut2 (* base cut1)))
    (+ (* cut2 (floor (/ n cut2))) (mod n cut1))))

(defun p-digit-replace (n i d &optional (base 10))
  "Replace number N's Ith digits with D.

Example:

     (p-digit-replace 123 1 4) ; => 143
     (p-digit-replace 123 1 0) ; => should equal to (p-digit-mask 123 1)

"
  (declare (type (integer 0) n i base))
  (let* ((cut1 (expt base i))
         (cut2 (* base cut1)))
    (+ (* cut2 (floor (/ n cut2)))
       (* d cut1)
       (mod n cut1))))

(defun p-digit-replace* (n i-list d &optional (base 10))
  "Replace N at I-LIST position by D. "
  (reduce (rcurry* #'p-digit-replace d base) i-list :initial-value n))

(defun count-prime-of-p-digit-replace* (n i-list &key (base 10) (replace (range-list 0 9)))
  "Count number of prime numbers by replacing N at I-LIST position with REPLACE. "
  (loop with digits = (count-digits n base)
        for rep in replace
        for new = (p-digit-replace* n i-list rep base)
        if (and (= (count-digits new base) digits) (primep new))
          collect new into primes
          and count new into len
        finally (return (values len primes))))

(defun problem51 (&optional (len 8))
  (loop for i from 1
        for p = (nth-prime i)
        for d = (count-digits p)
        do (loop with can-pick = (range-list 0 (1- d))
                 for pick from 1 below d
                 do (loop for replace in (n-pick-list can-pick pick)
                          do (multiple-value-bind (count primes)
                                 (count-prime-of-p-digit-replace* p replace)
                               (when (= count len)
                                 (return-from problem51 primes)))))))


;;; Problem 52. Permuted Multiples
;; It can be seen that the number, 125874, and its double, 251748,
;; contain exactly the same digits, but in a different order.
;;
;; Find the smallest positive integer, x, such that 2 * x, 3 * x, 4 * x,
;; 5 * x, and 6 * x, contain the same digits.
;;

;; Note that if x, 2x, 3x, 4x, 5x, and 6x should

(defun problem52 (&optional (n 6))
  "Return the smallest positive integer having the same digits. "
  (loop for start = 10 then (* 10 start) do
    (loop for x from (1+ start) upto (floor (* 10 start) 6)
          for xd = (count-p-digits x)
          if (and-repeat (i 2 n) (array= xd (count-p-digits (* i x))))
            do (return-from problem52 x))))


;;; Problem 53. Combinatoric Selections
;; There are exactly ten ways of selecting three from five, 12345:
;;
;;    123, 124, 125, 135, 135, 145, 234, 235, 245, and 345
;;
;;                                                  / 5 \
;; In combinatorics, we use the notation, C(n, r) = |   | = 10.
;;                                                  \ 3 /
;;
;; In general, C(n, r) = n! / r! (n - r)!, where r <= n,
;;
;;   n! = n * (n - 1) * ... * 3 * 2 * 1, and 0! = 1.
;;
;; It is not until n = 23, that a value exceeds one-million:
;; C(23, 10) = 1144066.
;;
;; How many, not necessarily distinct, values of C(n, r) for
;; 1 <= n <= 100, are greater than one-million?
;;

(defun choices (n r)
  "Return the C(n, r) = n! / r! (n - r)!. "
  (declare (type unsigned-byte n r))
  (assert (<= r n))
  (/ (factorial n) (* (factorial r) (factorial (- n r)))))

(defun problem53 (&optional (max 100) (limit +million+))
  "Count C(n, r) > million for 1 <= n <= MAX. "
  (loop with cnt = 0
        for n from 1 upto max
        for rmax = (ceiling n 2)
        do (loop for r from 1 upto rmax
                 if (> (choices n r) limit)
                   return (incf cnt (1+ (- n (* 2 r)))))
        finally (return cnt)))


;; Problem 54. Poker Hands
;; In the card game poker, a hand consists of five cards and are ranked,
;; from lowest to highest, in the following way:
;;
;; + High Card:       Highest value card
;; + One Pair:        Two cards of the same value
;; + Two Pairs:       Two different pairs
;; + Three of a Kind: Three cards of the same value
;; + Straight:        All cards are consecutive values
;; + Flush:           All cards of the same suit
;; + Full House:      Three of a kind and a pair
;; + Four of a Kind:  Four cards of the same value
;; + Straight Flush:  All cards are consecutive values of same suit
;; + Royal Flush:     Ten, Jack, Queen, King, Ace, in same suit.
;;
;; The cards are valued in the order:
;; 2, 3, 4, 5, 6, 7, 8, 9, 10, Jack, Queen, King, Ace.
;;
;; If two players have the same ranked hands then the rank made up
;; of the highest value wins: for example, a pair of eight beats
;; a pair of queens, then highest cards in each hand are compared
;; (see example 4 below); if the highest cards tie then the next
;; highest cards are compared, and so on.
;;
;; Consider the following five hands dealt to two players:
;;
;;     Hand      Player 1          Player 2         Winner
;;
;;      1     5H 5C 6S 7S KD    2C 3S 8S 8D TD     Player 2
;;            Pair of Fives     Pair of Eights
;;
;;      2     5D 8C 9S JS AC    2C 5C 7D 8S QH     Player 1
;;           Highest card Ace  Highest card Queen
;;
;;      3     2D 9C AS AH AC    3D 6D 7D TD QD     Player 2
;;              Three Aces     Flush with Diamonds
;;
;;      4     4D 6S 9H QH QC    3D 6D 7H QD QS     Player 1
;;            Pair of Queens    Pair of Queens
;;          Highest card Nine  Highest card Seven
;;
;;      5     2H 2D 4C 4D 4S    3C 3D 3S 9S 9D     Player 1
;;              Full House        Full House
;;           With Three Fours  with Three Threes
;;
;; The file, poker.txt, contains one-thousand random hands
;; dealt to two players. Each line of the file contains ten
;; cards (separated by a single space): the first five are
;; Player 1's cards and the last five are Player 2's cards.
;; You can assume that all hands are valid (no invalid
;; characters or repeated cards), each player's hand is in
;; no specific order, and in each hand there is a clear
;; winner.
;;
;; How many hands does Player 1 win?
;;

;; just use `str' package to cut down string manipulation time

(ql:quickload :str)

(deftype poker-card-color ()
  '(member :hearts :diamonds :clubs :spades))

(deftype poker-card-point ()
  '(integer 2 14))

(defstruct poker-card
  (point 0       :type poker-card-point)
  (color :hearts :type poker-card-color))

(defun poker-card<-string (string)
  "Turn poker card STRING into `poker-card'. "
  (declare (type string string))
  (let ((point (aref string 0))
        (color (aref string 1)))
    (make-poker-card :point (cond ((char= point #\A) 14)
                                  ((char= point #\K) 13)
                                  ((char= point #\Q) 12)
                                  ((char= point #\J) 11)
                                  ((char= point #\T) 10)
                                  (t (+ 2 (- (char-code point) (char-code #\2)))))
                     :color (cond ((char= color #\H) :hearts)
                                  ((char= color #\D) :diamonds)
                                  ((char= color #\C) :clubs)
                                  ((char= color #\S) :spades)))))

(defmethod print-object ((card poker-card) stream)
  (format stream "~C~C"
          (cond ((= (poker-card-point card) 10) #\T)
                ((= (poker-card-point card) 11) #\J)
                ((= (poker-card-point card) 12) #\Q)
                ((= (poker-card-point card) 13) #\K)
                ((= (poker-card-point card) 14) #\A)
                (t (code-char (+ (poker-card-point card) (char-code #\2) -2))))
          (ecase (poker-card-color card)
            (:hearts   #\H)
            (:diamonds #\D)
            (:clubs    #\C)
            (:spades   #\S))))

(defun read-poker-hands (file)
  "Read poker hands from FILE.
Return a list of (player1 player2). "
  (with-open-file (stream file)
    (loop for line = (read-line stream nil nil) while line
          for hand = (mapcar #'poker-card<-string (str:words line))
          collect (list (subseq hand 0 5) (subseq hand 5)))))

;; Poker Hands Score
;;
;;    15^0*02-14: High Card of 2-A
;;    15^1*02-14: One Pair of 2-A
;;    15^2*02-14: Second Pair of 2-A (max of second pair)
;;    15^3*02-14: Three of a Kind value
;;    15^4*02-14: Straight value
;;    15^5*02-14: Flush, value of High Card
;;    15^6*02-14: Full House:
;;    15^7*02-14: Four of a Kind, value of four
;;    15^8*02-14: Straight Flush, value of high card
;;    15^9*1:     Royal Flush
;;

(defun poker-hands (hands)
  "Return Poker hands score and type. "
  (destructuring-bind (first . rest) hands
    (let ((points (make-array 15 :initial-element 0 :element-type 'unsigned-byte))
          (color0 (poker-card-color first))
          (colorp t))
      (incf (aref points (poker-card-point first)))
      (dolist (card rest)
        (incf (aref points (poker-card-point card)))
        (unless (eq color0 (poker-card-color card))
          (setf colorp nil)))
      (when colorp
        (when (and-repeat (point 10 14)
                (= (aref points point) 1))
          (return-from poker-hands
            (values (expt 15 9) :royal-flush))))
      (loop with 2i1 = 0 with 2i2 = 0 with 3i  = 0
            for i from 2 upto 14
            for c = (aref points i)
            if (and colorp (= c 5))
              do (return-from poker-hands
                   (values (* (expt 15 8) i) :straight-flush))
            if (= c 4)
              do (return-from poker-hands
                   (values (* (expt 15 7) i) :four-of-a-kind))
            if (= c 3)
              do (setf 3i i)
            if (= c 2)
              do (if (zerop 2i1)
                     (setf 2i1 i)
                     (let ((min (min 2i1 i))
                           (max (max 2i1 i)))
                       (setf 2i1 min)
                       (setf 2i2 max)))
            if (/= c 0)
              maximize i into high-card
              and minimize i into row-start
            finally (return
                      (let ((type :high-card))
                        (values (+ high-card
                                   (if (zerop 2i1)
                                       0
                                       (progn (setf type :one-pair)
                                              (* 15 2i1)))
                                   (if (zerop 2i2)
                                       0
                                       (progn (setf type :two-pairs)
                                              (* (expt 15 2) 2i2)))
                                   (if (zerop 3i)
                                       0
                                       (progn (setf type :three-of-a-kind)
                                              (* (expt 15 3) 3i)))
                                   (if (loop for i from row-start upto 14
                                             while (= 1 (aref points i))
                                             count i into continue
                                             finally (return (= continue 5)))
                                       (progn (setf type :straight)
                                              (* (expt 15 4) (+ row-start 5)))
                                       0)
                                   (if colorp
                                       (progn (setf type :flush)
                                              (* (expt 15 5) high-card))
                                       0)
                                   (if (and (/= 2i2 0) (/= 3i 0))
                                       (progn (setf type :full-house)
                                              (expt 15 6))
                                       0))
                                type)))))))

(defun problem54 ()
  "Count how many times Player 1 wins. "
  (loop for (player1 player2) in (read-poker-hands "./dat/0054_poker.txt")
        for score1 = (poker-hands player1)
        for score2 = (poker-hands player2)
        count (> score1 score2)))


;;; Problem 55. Lychrel Numbers
;; If we take 47, reverse and add, 47 + 74 = 121, which is palindromic.
;;
;; Not all numbers produce palindromes so quickly. For example,
;;
;;      349 +  943 = 1292
;;     1292 + 2921 = 4213
;;     4213 + 3124 = 7337
;;
;; That is, 349 took three iterations to arrive at a palindrome.
;;
;; Although no one has proved it yet, it is thought that some
;; numbers, like 196, never produce a palindrome. A number that
;; never forms a palindrome through the reverse and add process
;; is called Lychrel number. Due to the theoretical nature of
;; these numbers, and for the purpose of this problem, we shall
;; assume that a number is Lychrel until proven otherwise. In
;; addition you are given that for every number below ten-thousand,
;; it will either:
;; (i) become a palindrome in less than fifty iterations, or
;; (ii) no one, with all the computing power that exists, has
;; managed so far to map it to a palindrome.
;;
;; In fact, 10677 is the first number to be shown to require over
;; fifty iterations before producing a palidrome:
;; 4668731596684224866951378664 (53 iterations, 28-digits).
;;
;; Surprisingly, there are palindromic numbers that are themselves
;; Lychrel numbers; the first example is 4994.
;;
;; How many Lychrel numbers are there below ten-thousand?
;;
;; NOTE: Wording was modified slightly on 24 April 2007 to emphasise
;; the theoretical nature of Lychrel numbers.
;;

(defun lychrel-number-p (num &optional (iteration 50))
  "Test if NUM is Lychrel Number within ITERATION. "
  (if (zerop iteration) t
      (let ((num (+ num (int<-p-digits (reverse (p-digits num))))))
        (unless (palindromep num)
          (lychrel-number-p num (1- iteration))))))

(defun problem55 (&optional (max (* 10 +thousand+)))
  "Count Lychrel numbers below ten-thousand. "
  (loop for i from 1 below max
        count (lychrel-number-p i)))


;;; Problem 56. Powerful Digit Sum
;; A googol (10^100) is massive number: one followed by one-hundred
;; zeros; 100^100 is almost unimaginably large: one followed by two-hundred
;; zeros. Despite their size, the sum of the digits in each number is
;; only 1.
;;
;; Considering natural of the form, a^b, where a, b < 100, what is the
;; maximum digital sum.
;;

(defun problem56 (&optional (max 100))
  "Return the max (sum (p-digits (expt a b))). "
  (loop for b from 2 below max
        maximize (loop for a from 1 below max
                       maximize (sum (p-digits (expt a b))))))


;;; Problem 57. Square Root Convergents
;; It is possible to show that the square root of two can be expressed as
;; an infinite continued fraction.
;;
;;       sqrt(2) = 1 + 1 / (2 + 1 / (2 + 1 / (2 + ... )))
;;
;; By expanding this for the first four iterations, we get:
;;
;;  1 + 1/2                         =  3/2  = 1.5
;;  1 + 1/(2 + 1/2)                 =  7/5  = 1.4
;;  1 + 1/(2 + 1/(2 + 1/2))         = 17/12 = 1.41666...
;;  1 + 1/(2 + 1/(2 + 1/(2 + 1/2))) = 41/29 = 1/41379...
;;
;; The next three expansions are 99/70, 239/169, and 577/408, but
;; the eighth expansion, 1393/985, is the first example where
;; the number of digits in the numerator exceeds the number of
;; digits in the denominator.
;;
;; In the first one-thousand expansions, how many fractions
;; contain a numerator with more digits than the denominator?
;;

;; x(n+1) = 1/(1 + x(n))

(defun square-root-2-frac-iteration (frac)
  "Iterate on 1 + 1/(2 + 1/(2 + 1/(2 + ...))). "
  (declare (type rational frac))
  (1+ (/ (1+ frac))))

(defun problem57 (&optional (max +thousand+))
  "Count numerator digits > denominator digits. "
  (loop repeat max
        for xi = 3/2 then (square-root-2-frac-iteration xi)
        for num = (numerator   xi)
        for den = (denominator xi)
        count (> (count-digits num) (count-digits den))))


;;; Problem 58. Spiral Primes
;; Starting with 1 and spiralling anticlockwise in the following way,
;; a square spiral with side length 7 is formed.
;;
;;        37 36 35 34 33 32 31
;;        38 17 16 15 14 13 30
;;        39 18  5  4  3 12 29
;;        40 19  6  1  2 11 28
;;        41 20  7  8  9 10 27
;;        42 21 22 23 24 25 26
;;        43 44 45 46 47 48 49
;;
;; It is interesting to note that the odd seuares lie along the bottom
;; right diagonal, but what is more interesting is that 8 out of the
;; 13 numbers lying along both diagonals are pime; that is, a ratio
;; of 8/13 = 62%.
;;
;; If one complete new layer is wrapped around the spiral above, a
;; square spiral with side length 9 will be formed. If this process
;; is continued, what is the side length of the square spiral for
;; which the ratio of primes along both diagonals first falls below
;; 10%.
;;

;; see `problem28'

(defun make-spiral-corners-iterator ()
  "Make a iterator function that return a list of corners and nth layer. "
  (let ((layer 2)
        (num   1)
        (width 3))
    (lambda ()
      (loop with corners = (list (incf num (1+ (- width 2))))
            repeat 3
            do (push (incf num (1- width)) corners)
            finally (return (unwind-protect (values corners layer)
                              (incf layer)
                              (incf width 2)))))))

(defun select (testf sequence &key key)
  "Select by TESTF on SEQUENCE. "
  (remove-if-not testf sequence :key key))

(defun problem58 (&optional (start 4) (limit 0.1))
  "Return the sum of the diagonals. "
  (loop with iter = (make-spiral-corners-iterator)
        for (corners layer) = (multiple-value-list (funcall iter))
        for total  from 5 by 4
        for primes = (count-if #'primep corners)
          then (+ primes (count-if #'primep corners))
        while (or (< layer start)
                  (>= (/ primes total) limit))
        finally (return (values (1- (* 2 layer)) (/ primes total)))))


;;; Problem 59. XOR Decryption
;; Each character on a computer is assigned a unique code and the preferred
;; standard is ASCII (American Standard Code for Information Interchange).
;; For example, uppercase A = 65, asterisk (*) = 42, and lowercase k = 107.
;;
;; A modern encryptioin method is to take a text file, convert the bytes
;; to ASCII, then XOR each byte with a given value, taken from a secret key.
;; The advantage with the XOR function is that using the same encryption key
;; on the cipher text, restores the plain text; for example, 65 XOR 42 = 107,
;; then 107 XOR 42 = 65.
;;
;; For unbreakable encryption, the key is the same length as the plain text
;; message, and teh key is made up of random bytes. The user would keep the
;; encrypted message and the encryption key in different locations, and
;; without both "halves", it is impossible to decrypt the message.
;;
;; Unfortunately, this method is impractical for most users, so the modified
;; method is to use a password as a key. If the password is shorter than the
;; message, which is likely, the key is repeated cyclically thoughout the
;; message. The balance for this method is using a sufficiently long password
;; key for security, but short enough to be memorable.
;;
;; Your task has been made easy, as the encryption key consists of three lower
;; case characters. Using ./dat/0059_cipher.sexp, a file containing the
;; encrypted ASCII codes, and the knowledge that the plain text must contain
;; common English words, decrypt the message and find the sum of the ASCII
;; values in the original text.
;;

(defun xor-list (list1 list2)
  "XOR each element for LIST1 and LIST2.
If one list is shorter than another list, windowed map it. "
  (let ((len1 (length list1))
        (len2 (length list2)))
    (cond ((= len1 len2)
           (mapcar #'logxor list1 list2))
          ((< len1 len2)
           (apply #'append
                  (windowed-mapcar
                   (compose (curry #'xor-list list1) #'args) len1 list2 len1)))
          (t
           (apply #'append
                  (windowed-mapcar
                   (compose (curry #'xor-list list2) #'args) len2 list1 len2))))))

;; Just need some brute force to manually fine tuning FIRST-N
;; to cut down the time (since the `english-like-p' is not so
;; easy to determine

(defun problem59 ()
  "Decrypt the message. "
  (let ((message (read-file "./dat/0059_cipher.sexp")))
    (flet ((english-like-p (string)
             (and-repeat (i (length string))
               (let ((chr (aref string i)))
                 (or (char<= #\A chr #\Z)
                     (char<= #\a chr #\z)
                     (char<= #\0 chr #\9)
                     (find chr '(#\Space #\" #\/ #\, #\' #\( #\)
                                 #\[ #\] #\+ #\- #\: #\; #\.)
                           :test #'char=))))))
      (loop for p1 from (char-code #\a) upto (char-code #\z) do
        (loop for p2 from (char-code #\a) upto (char-code #\z) do
          (loop for p3 from (char-code #\a) upto (char-code #\z)
                for passwd = (list p1 p2 p3)
                for dec = (xor-list passwd message)
                if (english-like-p (map 'string #'code-char dec))
                  do (return-from problem59
                       (values (sum dec)
                               (map 'string #'code-char passwd)
                               (map 'string #'code-char dec)))))))))


;;; Problem 60. Prime Pair Sets
;; The primes 3, 7, 109, and 673, are quite remarkable. By taking any
;; two primes and concatenating them in any order the result will
;; always be prime. For example, taking 7 and 109, both 7109 and 1097
;; are prime. The sum of these four primes, 792, represents the lowest
;; sum for a set of four primes with this property.
;;
;; Find the lowest sum for a set of five primes for which any two
;; primes concatenate to produce another prime.
;;

(defun p-digit-concate (n1 n2 &optional (base 10))
  "Concatenate N1 and N2. "
  (int<-p-digits (append (p-digits n1 base) (p-digits n2 base)) base))

(defun any-p-digit-concate-prime-p (primes)
  "Test if any p-digit-concate of PRIMES are prime. "
  (and-dolist (p1p2 (n-pick-list primes 2))
    (primep (apply #'p-digit-concate p1p2))))

;; Algorithm:
;; p-concate-prime-p(p1, p2) = (primep * p-digit-concate) (p1, p2)
;;
;; find-primes(0) = ()
;; find-primes(1) = (any prime)
;; find-primes(2) = (p1, p2 that is p-concate-prime-p(p1, p2))
;; find-primes(n) = (p1..pn-1, pn that is p-concate-prime-p(pi, pn), i = 1, n-1)
;;

(defun problem60 (&optional (n 5) (limit 1100))
  "Search for N more primes that could make them with PRIMES
any-p-digit-concate-prime. "
  (labels ((find-primes (rest primes start)
             (if (zerop rest) primes
                 (loop for i from start below limit for p1 = (nth-prime i)
                       if (and-dolist (p2 primes)
                            (and (primep (p-digit-concate p1 p2))
                                 (primep (p-digit-concate p2 p1))))
                         do (let ((primes (find-primes
                                           (1- rest) (cons p1 primes) (1+ i))))
                              (when primes
                                (return primes)))))))
    (sum (find-primes n () 2))))

;;; Problem 61. Cyclical Figurate Numbers
;; Triangle, square, pentagonal, hexagonal, heptagonal, and octagonal
;; numbers are all figurate (polygonal) numbers and are generated by
;; the following formulae:
;;
;;  Triangle     P(3, n) = n * (n + 1) / 2        1, 3,  6, 10, 15, ...
;;  Square       P(4, n) = n^2                    1, 4,  9, 16, 25, ...
;;  Pentagonal   P(5, n) = n * (3 * n - 1) / 2    1, 5, 12, 22, 35, ...
;;  Hexagonal    P(6, n) = n * (2 * n - 1)        1, 6, 15, 28, 45, ...
;;  Heptagonal   P(7, n) = n * (5 * n - 3) / 2    1, 7, 18, 34, 55, ...
;;  Octagonal    P(8, n) = n * (3 * n - 2)        1, 8, 21, 40, 65, ...
;;
;; The ordered set of three 4-digit numbers: 8128, 2882, 8281, has
;; three interesting properties.
;;
;;  1. The set is cyclic, in that the last two digits of each number
;;     is the first two digits of the next number (including the last
;;     number with the first).
;;  2. Each polygonal type: triangle (P(3, 127) = 8128), square
;;     (P(4, 91) = 8281), and pentagonal (P(5, 44) = 2882), is
;;     represented by a different number in the set.
;;  3. This is the only set of 4-digit numbers with this property.
;;
;; Find the sum of the only ordered set of six cyclic 4-digit numbers
;; for which each polygonal type: triangle, square, pentagonal,
;; hexagonal, heptagonal, and octagonal, is represented by a different
;; number in the set.
;;

(defun heptagonal-number (n)
  "Return n * (5 * n - 3) / 2. "
  (/ (* n (- (* 5 n) 3)) 2))

(defun heptagonal-number-p (n)
  "Test if N is Heptagonal number. "
  (multiple-value-bind (sqrtp sqrt)
      (integer-square-p (+ 9 (* 40 n)))
    (if sqrtp
        (let ((num (+ 3 sqrt)))
          (if (modp num 10)
              (values t (/ num 10))
              (values nil nil)))
        (values nil nil))))

(defun octagonal-number (n)
  "Return n * (3 * n - 2). "
  (* n (- (* 3 n) 2)))

(defun octagonal-number-p (n)
  "Test if N is Octagonal number. "
  (multiple-value-bind (sqrtp sqrt)
      (integer-square-p (1+ (* 3 n)))
    (if sqrtp
        (let ((num (1+ sqrt)))
          (if (modp num 3)
              (values t   (/ num 3))
              (values nil nil)))
        (values nil nil))))

(defun cyclic-digits-list-p (list size &optional (base 10))
  "Test if LIST is a list of Cyclic digits.
The SIZE is the Cyclic part size.

Example:

    (cyclic-digits-list-p '(8128 2882 8281) 2) ; => t
"
  (loop with 1st  = (p-digits (first list) base)
        with last = (int<-p-digits (subseq 1st 0 size) base)
        with prev = (int<-p-digits (last   1st size)   base)
        for elem in (rest list)
        for digit = (p-digits elem)
        for head = (int<-p-digits (subseq digit 0 size) base)
        for tail = (int<-p-digits (last   digit size)   base)
        if (not (= prev head))
          return nil
        do (setf prev tail)
        finally (return (equal tail last))))

(defun square-number (n)
  "Return n^2. "
  (square n))

(defun square-number-p (n)
  "Test if N is Square number. "
  (integer-square-p n))

;; Algorithm:
;; for given PREV at i-th position, find the NEXT that
;; satisfy (test i) that ((test i) (+ (* PREV 100) NEXT)).
;; if satisfies, search next or otherwise, return nil.

(defun problem61 (&optional (tests (list #'triangle-number-p
                                         #'square-number-p
                                         #'pentagonal-number-p
                                         #'hexagonal-number-p
                                         #'heptagonal-number-p
                                         #'octagonal-number-p))
                    (digits 2))
  "Return the sum of cyclic 4-digit. "
  (let ((shift (expt 10 digits))
        (min   (expt 10 (1- digits)))
        (max   (1- (expt 10 digits))))
    (labels ((iter (test rest prev tail)
               (if (endp rest)
                   (let ((num (+ (* prev shift) tail)))
                     (when (funcall test num)
                       (list num)))
                   (loop for next from min upto max
                         for num = (+ (* prev shift) next)
                         for seq = (when (funcall test num)
                                     (iter (car rest) (cdr rest) next tail))
                         if seq return (cons num seq)))))
      (loop for test-seq in (permutation-list tests) do
        (loop for tail from min upto max
              for seq = (iter (car test-seq) (cdr test-seq) tail tail)
              if seq do (return-from problem61 (values (sum seq) seq)))))))


;;; Problem 62. Cubic Permutations
;; The cube, 41063625 (345^3), can be permuted to produce two other cubes:
;; 56623104 (384^3) and 66431025 (405^3). In fact, 41063625 is the smallest
;; cube which has exactly three permutations of its digits which are also
;; cube.
;;
;; Find the smallest cube for which exactly five permutations of its
;; digits are cube.
;;

(defun cube (x)
  "Return x^3. "
  (* x (* x x)))

;; Newton's method
;; x = (2 * x + n / x^2) / 3

(defun integer-cube-p (x)
  "Test if X is n^3. "
  (loop for x1 = x then x2
        for x2 = (truncate (+ (* 2 x1) (truncate x (* x1 x1))) 3)
        if (>= x2 x1)
          return (if (= (cube x1) x)
                     (values t   x1)
                     (values nil nil))))

(defun problem62 (&optional (count 5))
  "Find the smallest cube has COUNT permutations. "
  (loop with cnts = (make-hash-table :test 'equal)
        for i from 1
        for cube = (cube i)
        for key  = (sort (p-digits cube) #'<)
        for (val . cnt) = (or (gethash key cnts)
                              (cons cube 0))
        for cnt* = (1+ cnt)
        if (= cnt* count)
          return val
        do (setf (gethash key cnts) (cons val cnt*))))


;;; Problem 63. Powerful Digit Counts
;; The 5-digit number, 16807 = 7^5, is also a fifth power. Similarly,
;; the 9-digit number, 134217728 = 8^9, is a ninth power.
;;
;; How many n-digit positive integers exist which are also an nth power?
;;

;;    1 = 1^1
;;   16 = 4^2
;;  729 = 9^3
;; 6561 = 9^4
;;  ... = ...
;;

(defun problem63 ()
  "Count n-digit positive integers as nth power. "
  (loop with count = 0
        with pattern = ()
        for n from 1
        while (loop with modifiedp = nil
                    for base from 1
                    for num  = (expt base n)
                    for digits = (count-digits num)
                    if (= digits n)
                      do (push (list base n num digits) pattern)
                      and do (setf count (1+ count)
                                   modifiedp t)
                    if (> digits n) ; if cannot find base more
                      return modifiedp)
        finally (return (values count pattern))))


;;; Problem 64. Odd Period Square Roots
;; All square roots are periodic when written as continued fractions
;; and can be written in the form:
;;
;;    sqrt(N) = a0 + 1 / (a1 + 1 / (a2 + 1 / (a3 + ...)))
;;
;; For example, let us consider sqrt(23):
;;
;;    sqrt(23) = 4 + sqrt(23) - 4 = 4 + 1 / (1 / (sqrt(23) - 4))
;;
;; The process can be summarised as follows:
;;
;;    a0 = 4, 1 / (sqrt(23) - 4) =     (sqrt(23) + 4) /  7 = 1 + (sqrt(23) - 3) / 7
;;    a1 = 1, 7 / (sqrt(23) - 3) = 7 * (sqrt(23) + 3) / 14 = 3 + (sqrt(23) - 3) / 2
;;    a2 = 3, 2 / (sqrt(23) - 3) = 2 * (sqrt(23) + 3) / 14 = 1 + (sqrt(23) - 4) / 7
;;    a3 = 1, 7 / (sqrt(23) - 4) = 7 * (sqrt(23) + 4) /  7 = 8 + (sqrt(23) - 4)
;;    a4 = 8, 1 / (sqrt(23) - 4) =     (sqrt(23) + 4) /  7 = 1 + (sqrt(23) - 3) / 7
;;    a5 = 1, 7 / (sqrt(23) - 3) = 7 * (sqrt(23) + 3) / 14 = 3 + (sqrt(23) - 3) / 2
;;    a6 = 3, 7 / (sqrt(23) - 3) = 2 * (sqrt(23) + 3) / 14 = 1 + (sqrt(23) - 4) / 7
;;    a7 = 1, 7 / (sqrt(23) - 4) = 7 * (sqrt(23) + 4) /  7 = 8 + (sqrt(23) - 4)
;;
;; It can be seen that the sequence is repeating. For conciseness, we use
;; the notation sqrt(23) = [4; (1, 2, 1, 8)], to indicate that the block
;; (1, 3, 1, 8) repeats indefinitely.
;;
;; The first ten continued fraction representations of (irrational)
;; square roots are:
;;
;;    sqrt(2) = [1; (2)],             period = 1
;;    sqrt(3) = [1; (1, 2)],          period = 2
;;    sqrt(5) = [2; (4)],             period = 1
;;    sqrt(6) = [2; (2, 4)],          period = 2
;;    sqrt(7) = [2; (1, 1, 1, 4)],    period = 4
;;    sqrt(8) = [2; (1, 4)],          period = 2
;;   sqrt(10) = [3; (6)],             period = 1
;;   sqrt(11) = [3; (3, 6)],          period = 2
;;   sqrt(12) = [3; (2, 6)],          period = 2
;;   sqrt(13) = [3; (1, 1, 1, 1, 6)], period = 5
;;
;; Extract four continued fractions, for N <= 13, have an odd period.
;;
;; How many continued fractions for N <= 10000 have an odd period.
;;

;; Notice that:
;;
;;    a0 = truncate(sqrt(x))
;;
;;    ni / (sqrt(x) - d)
;;    = ni * (sqrt(x) + di) / (x - di^2) => (sqrt(x) + di) / D
;;    = ai+1 + (sqrt(x) - di+1) / ni+1
;;
;;    => ni+1 = (x - di^2) / ni
;;    => ai+1 = truncate(ni / (sqrt(x) - di))
;;    => di+1 = ai+1 * ni+1 - di
;;

(defun integer-sqrt-cycle (x)
  "Return a list of (a0 . (a1 a2 a3 ...)). "
  (let ((sqrt (sqrt x))
        (a0   (isqrt x)))
    (labels ((iter (ai ni di ands)
               (let* ((ni+1 (/ (- x (square di)) ni))
                      (ai+1 (truncate ni (- sqrt di)))
                      (di+1 (- (* ai+1 ni+1) di)))
                 (if (find (list ai+1 ni+1 di+1) ands :test #'equal)
                     (list ai)
                     (cons ai (iter ai+1 ni+1 di+1
                                    (cons (list ai+1 ni+1 di+1) ands)))))))
      (if (= (square a0) x)
          (values () a0)
          (values (cdr (iter a0 1 a0 (list (list a0 1 a0)))) a0)))))

(defun problem64 (&optional (max 10000))
  "Count odd period fractions upto MAX. "
  (loop for n below max
        count (oddp (length (integer-sqrt-cycle n)))))


;;; Problem 65. Convergents of e
;; The square root of 2 can be written as an infinite continued fraction.
;;
;;     sqrt(2) = 1 + 1 / (2 + 1 / (2 + 1 / ...))
;;
;; The infinite continued fraction can be written, sqrt(2) = [1; (2)],
;; (2) indicates that 2 repeats ad infinitum. In a similar way,
;; sqrt(23) = [4; (1, 3, 1, 8)].
;;
;; It turns out that the sequence of partial values of continued fractions
;; for square roots provide the best rational approximations. Let us
;; consider the convergents for sqrt(2).
;;
;;    1 + 1/2                               = 3/2
;;    1 + 1 / (2 + 1/2)                     = 7/5
;;    1 + 1 / (2 + 1 / (2 + 1/2))           = 17/12
;;    1 + 1 / (2 + 1 / (2 + 1 / (2 + 1/2))) = 41/29
;;
;; Hence the sequence of the first ten convergents for sqrt(2) are:
;;
;;    1, 3/2, 7/5, 41/29, 99/70, 239/169, 577/408, 1393/985, 3363/2378, ...
;;
;; What is most surprising is that the important mathematical constant,
;;
;;    e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, ..., 2 * k, 1, ...]
;;
;; The first ten terms in the sequence of convergents for e are:
;;
;;    2, 3, 8/3, 11/4, 19/7, 87/32, 106/39, 193/71, 1264/465, 1457/536, ...
;;
;; The sum of digits in the numerator of the 10th convergent is 1 + 4 + 5 + 7 = 17.
;;
;; Find the sum of digits in the numerator of 100th convergent of the
;; continued fraction for e.
;;

(defun convergents<-regular-continued-fraction1 (int fractions)
  "Turn [n, (fractions)] into a convergent value.

Example:

    sqrt(2) = (... 1 '(2 2 2))
            = 1 + 1/(2 + 1/(2 + 1/(2)))
"
  (labels ((unfold (fractions)
             (if (endp fractions) 0
                 (/ (+ (car fractions) (unfold (cdr fractions)))))))
    (+ int (unfold fractions))))

(defun problem65 (&optional (nth 100))
  "Return the sum of digits of NTH numerator convergent of e. "
  (funcall (compose (compose #'sum #'p-digits) #'numerator)
           (convergents<-regular-continued-fraction1
            2
            (loop with k = 0
                  with i = 1
                  for cnt from 1 below nth
                  if (zerop i)
                    collect (* 2 (incf k))
                    and do (setf i 2)
                  else
                    collect 1
                    and do (decf i)))))


;;; Problem 66. Diophantine Equation
;; Consider quadratic Diophantine equations of the form:
;;
;;    x^2 - D * y^2 = 1
;;
;; For example, when D = 13, the minimal solution in x is
;; 649^2 - 13 * 180^2 = 1.
;;
;; It can be assumed that there are no solutions in positive
;; integers when D is square.
;;
;; By finding minimal solutions in x for D = {2, 3, 5, 6, 7},
;; we obtain the following:
;;
;;    3^2 - 2 * 2^2 = 1
;;    2^2 - 3 * 1^2 = 1
;;    9^2 - 5 * 4^2 = 1
;;    5^2 - 6 * 2^2 = 1
;;    8^2 - 7 * 3^2 = 1
;;
;; Hence, by considering minimal solutions in x for D <= 7,
;; the largest x is obtained when D = 5.
;;
;; Find the value of D <= 1000 in minimal solutions of x for
;; which the largest value of x is obtained.
;;

;; Pell's Equation
;; see https://en.wikipedia.org/wiki/Pell%27s_equation
;;
;; this is much faster than counting directly

(defun pells-equation-fundamental-solution (d)
  "Find the minimal root of x^2 - D * y^2 = 1. "
  (multiple-value-bind (fractions int)
      (integer-sqrt-cycle d)
    (when fractions
      (let ((conv (if (evenp (length fractions))
                      (convergents<-regular-continued-fraction1
                       int (butlast fractions))
                      (convergents<-regular-continued-fraction1
                       int (append fractions (butlast fractions))))))
        (values (numerator conv) (denominator conv))))))

(defun problem66 (&optional (dmax 1000))
  "Return the max of `find-min-x^2-d*y^2=1' result x. "
  (loop with max = 0
        with max-d = 0
        for d from 1 upto dmax
        for x = (pells-equation-fundamental-solution d)
        do (print (list d x))
        if (and x (< max x))
          do (setf max   x
                   max-d d)
        finally (return max-d)))


;;; Problem 67. Maximum Path Sum II
;; see Problem 18.
;;

(defun problem67 ()
  "see problem 18. "
  (problem18 (read-file "./dat/0067_triangle.sexp")))


;;; Problem 68. Magic 5-gon Ring
;; Consider the following "magic" 3-gon ring, filled with the numbers 1 to 6,
;; and each line adding to nine.
;;
;;
;;          4                         0
;;            \                         \
;;             3                         2
;;            /  \                      /  \
;;           1 -- 2 -- 6               1 -- 0 -- 1
;;          /                         /
;;        5                         2
;;
;; Working clockwise, and starting from the group of three with the
;; numerically lowest external node (4, 3, 2, in this example),
;; each solution can be described uniquely. For example, the above
;; solution can be described by the set: 4,3,2; 6,2,1; 5,1,3.
;;
;; It is possible to complete the ring with four different totals:
;; 9, 10, 11, and 12. There are eight solutions in total.
;;
;;     Total            Solution Set
;;       9            4,2,3; 5,3,1; 6,1,2
;;       9            4,3,2; 6,2,1; 5,1,3
;;      10            2,3,5; 4,5,1; 6,1,3
;;      10            2,5,3; 6,3,1; 4,1,5
;;      11            1,4,6; 3,6,2; 5,2,4
;;      11            1,6,4; 5,4,2; 3,2,6
;;      12            1,5,6; 2,6,4; 3,4,5
;;      12            1,6,5; 3,5,4; 2,4,6
;;
;; By concatenating each group it is possible to form 9-digit strings;
;; the maximum string for a 3-gon ring is 432621513.
;;
;; Using the numbers 1 to 10, and depending on arrangements, it
;; is possible to form 16-and 17-digit strings. What is the maximum
;; 16-digit string for a "magic" 5-gon ring?
;;
;;
;;           ()
;;             \
;;              ()  ()
;;             /  \ |
;;           ()     ()
;;          / |     |
;;        () () --- () -- ()
;;            |
;;           ()
;;

(defstruct n-gon-ring
  (min   1  :type (integer 0))
  (max   10 :type (integer 0))
  (n     3  :type (integer 3))
  (inner (make-array 3 :initial-element 0
                       :element-type    'integer)
   :type array)
  (outter (make-array 3 :initial-element 0
                        :element-type    'integer)
   :type array))

(defun n-gon-ring (n &key (min 1) (max 10) (initial-contents () initial-contents-p))
  "Make magick N gon ring. "
  (let* ((inner  (make-array n :initial-element -1
                               :element-type    'integer))
         (outter (make-array n :initial-element -1
                               :element-type    'integer))
         (ring   (make-n-gon-ring :min    min
                                  :max    max
                                  :n      n
                                  :inner  inner
                                  :outter outter)))
    ;;                                     r1
    ;;          4                         0
    ;;            \                         \ r2
    ;;             3                         2       -----------+
    ;;            /  \                      /  \ r3             |
    ;;           1 -- 2 -- 6               1 -- 0 -- 1          |
    ;;          /                         / R3   R2   R1  <-----+
    ;;        5                         2
    (when initial-contents-p
      (assert (= n (length initial-contents)))
      (loop for i0 from 0
            for i1 = i0
            for i2 = (mod (1- i0) n)
            for i3 = (mod i0      n)
            for (r1 r2 r3) in initial-contents
            do (setf (aref outter i1) r1)
            do (if (= -1 (aref inner i2))
                   (setf (aref inner i2) r2)
                   (assert (= r2 (aref inner i2))))
            do (if (= -1 (aref inner i3))
                   (setf (aref inner i3) r3)
                   (assert (= r3 (aref inner i3))))))
    ring))

(defmethod print-object ((ring n-gon-ring) stream)
  (print-unreadable-object (ring stream)
    (let ((inner  (n-gon-ring-inner  ring))
          (outter (n-gon-ring-outter ring))
          (n      (n-gon-ring-n      ring)))
      (format stream "~D gon ring: " n)
      (loop for i0 from 0 below n
            for i1 = i0
            for i2 = (mod (1- i0) n)
            for i3 = (mod i0      n)
            for r1 = (aref outter i1)
            for r2 = (aref inner  i2)
            for r3 = (aref inner  i3)
            do (format stream "~D,~D,~D; " r1 r2 r3)))))

(defun n-gon-ring<-string (string)
  "Turn STRING into n-gon-ring. "
  (let ((contents (mapcar (compose (curry #'mapcar #'parse-integer)
                                   (curry #'str:split-omit-nulls ","))
                          (str:split-omit-nulls ";" string))))
    (assert (mapcar (compose (curry #'= 3) #'length) contents))
    (n-gon-ring (length contents) :initial-contents contents)))

(defun list<-n-gon-ring (ring)
  "Turn RING into list. "
  (let ((inner  (n-gon-ring-inner  ring))
        (outter (n-gon-ring-outter ring))
        (n      (n-gon-ring-n      ring)))
    (loop for i0 from 0 below n
          for i1 = i0
          for i2 = (mod (1- i0) n)
          for i3 = (mod i0      n)
          for r1 = (aref outter i1)
          for r2 = (aref inner  i2)
          for r3 = (aref inner  i3)
          collect (list r1 r2 r3))))

(defun copy-n-gon-ring (ring)
  "Copy RING. "
  (n-gon-ring (n-gon-ring-n ring)
              :min (n-gon-ring-min ring)
              :max (n-gon-ring-max ring)
              :initial-contents (list<-n-gon-ring ring)))

(defun n-gon-ring= (ring1 ring2)
  "Test if RING1 is equal to RING2. "
  (let ((n1 (n-gon-ring-n ring1))
        (n2 (n-gon-ring-n ring2)))
    (when (= n1 n2)
      (let ((inner1  (n-gon-ring-inner  ring1))
            (inner2  (n-gon-ring-inner  ring2))
            (outter1 (n-gon-ring-outter ring1))
            (outter2 (n-gon-ring-outter ring2)))
        ;;                                     r1
        ;;          4                         0
        ;;            \                         \ r2
        ;;             3                   r3*   2       -----------+
        ;;            /  \                      /  \ r3             |
        ;;           1 -- 2 -- 6        r2*    1 -- 0 -- 1          |
        ;;          /                         / R3   R2   R1  <-----+
        ;;        5                   r1*    2
        (loop with n = n1
              for offset from 0 below n
              if (and-repeat (i n)
                   (let ((i3 i)               (i3* (mod (+ i      offset) n))
                         (i2 (mod (1- i) n))  (i2* (mod (+ (1- i) offset) n))
                         (i1 i)               (i1* (mod (+ i      offset) n)))
                     (and (= (aref inner1  i3) (aref inner2  i3*))
                          (= (aref inner1  i2) (aref inner2  i2*))
                          (= (aref outter1 i1) (aref outter2 i1*)))))
                return t)))))

(defun subtract-list (list1 list2 &optional key test)
  "Return a list with elements in LIST1 but not in LIST2. "
  (remove-if (rcurry* #'find list2 :key key :test test) list1))

;; Algorithm:
;; 0. let all the possible choices list as PICKS
;;    pick 3 elements from PICKS and remove them from PICKS
;;    set the 3 elements to the first row (r1, r2, r3)
;;    let TOTAL = sum(3 elements)
;; 1. for second row:
;;    pick one from PICKS as R3
;;    the R2 is determinated from previous row
;;    calculate R1 = TOTAL - R2 - R3
;;    if R1 is within PICKS, stop (failed search)
;;    otherwise, repeat process for next row (third row)
;; 2. if find a new, collect them
;;
;; emmm, is it's like filling sudoku?
;;

(defun try-fill-ring (n &key (min 1) (max 10))
  "Try to fill the N gon ring.
Return a list of all the possible ring. "
  (declare (type (integer 3) n))
  (let* ((ring   (n-gon-ring n :min min :max max))
         (inner  (n-gon-ring-inner  ring))
         (outter (n-gon-ring-outter ring))
         (result ()))
    ;;                                     r1
    ;;          4                         0
    ;;            \                         \ r2
    ;;             3                   r3*   2       -----------+
    ;;            /  \                      /  \ r3             |
    ;;           1 -- 2 -- 6        r2*    1 -- 0 -- 1          |
    ;;          /                         / R3   R2   R1  <-----+
    ;;        5                   r1*    2
    (labels ((iter (total i3 picks)
               (if (= i3 (1- n))
                   ;; for the last row in ring,
                   ;; r2*, r3* is setted before, r1* is determined by:
                   ;; r1* = total - r2* - r3*
                   (let* ((i2 (mod (1- i3) n))
                          (i1 i3)
                          (r2 (aref inner i2))
                          (r3 (aref inner i3))
                          (r1 (- total r2 r3)))
                     ;; If R1 is pickable from PICKS,
                     ;; collect TOTAL and RING
                     (when (find r1 picks)
                       (setf (aref outter i1) r1)
                       (push (cons total (copy-n-gon-ring ring)) result)))
                   ;; for the row (not the last) in ring
                   ;; R2 is setted before,
                   ;; pick one R3 from PICKS,
                   ;; R1 = total - R2 - R3
                   ;; if R1 is found in PICKS,
                   ;; search next row
                   ;; otherwise, try next R2
                   (loop with i2 = (mod (1- i3) n)
                         with i1 = i3
                         with r2 = (aref inner i2)
                         for unfold = () then (cons r3 unfold)
                         for (r3 . folded) on picks
                         for r1 = (- total r2 r3)
                         if (find r1 unfold)
                           do (setf (aref inner  i3) r3
                                    (aref outter i1) r1)
                           and do (iter total (1+ i3) (append (remove r1 unfold)
                                                              folded))
                         if (find r1 folded)
                           do (setf (aref inner  i3) r3
                                    (aref outter i1) r1)
                           and do (iter total (1+ i3) (append (remove r1 folded)
                                                              unfold))))))
      ;; Set specific initial n gon ring
      (loop with choices = (range-list min max)
            for 1st-row in (n-pick-list choices 3)
            for picks = (subtract-list choices 1st-row)
            do (loop for (r1 r2 r3) in (permutation-list 1st-row)
                     do (setf (aref outter 0)      r1)
                     do (setf (aref inner  (1- n)) r2)
                     do (setf (aref inner  0)      r3)
                     do (iter (+ r1 r2 r3) 1 picks)))
      (group result :key #'car
                    :reduce (lambda (new collects)
                              (if (find-if (curry #'n-gon-ring= (cdr new)) collects)
                                  collects
                                  (cons (cdr new) collects)))
                    :initial-value ()))))

(defun clockwise-string<-n-gon-ring (ring)
  "Turn RING into clockwise string. "
  (with-output-to-string (str)
    (loop with i1-min = 0 with r1-min = -1
          with n      = (n-gon-ring-n      ring)
          with inner  = (n-gon-ring-inner  ring)
          with outter = (n-gon-ring-outter ring)
          for i1 from 0 below n
          for r1 = (aref outter i1)
          if (or (= r1-min -1) (< r1 r1-min))
            do (setf i1-min i1
                     r1-min r1)
          finally (loop repeat n
                        for i1 = i1-min then (mod (1+ i1) n)
                        for i2 = (mod (1- i1) n)
                        for i3 = i1
                        collect (format str "~D~D~D"
                                        (aref outter i1)
                                        (aref inner  i2)
                                        (aref inner  i3))))))

(defun problem68 ()
  "Return the maxim 16-digit string. "
  (loop with max = ""
        for ring in (apply #'append (mapcar #'cdr (try-fill-ring 5 :min 1 :max 10)))
        for digits = (clockwise-string<-n-gon-ring ring)
        if (and (= 16 (length digits)) (string< max digits))
          do (setf max digits)
        finally (return max)))


;;; Problem 69. Totient Maximum
;; Euler's totient function, phi(n) [sometimes called the phi function],
;; is defined as the number of positive integers not exceeding n which
;; are relatively prime to n. For example, as 1, 2, 4, 5, 7, and 8, are
;; all less than or equal to nine and relatively prime to nine, phi(9) = 6.
;;
;;     |  n | Relatively Prime | phi(n) | n / phi(n) |
;;     |----+------------------+--------+------------|
;;     |  2 |        1         |   1    |     2      |
;;     |  3 |      1, 2        |   2    |    1.5     |
;;     |  4 |      1, 3        |   2    |     2      |
;;     |  5 |    1, 2, 3, 4    |   4    |   1.25     |
;;     |  6 |      1, 5        |   2    |     3      |
;;     |  7 | 1, 2, 3, 4, 5, 6 |   6    |  1.1666... |
;;     |  8 |    1, 3, 5, 7    |   4    |     2      |
;;     |  9 | 1, 2, 4, 5, 7, 8 |   6    |    1.5     |
;;     | 10 |    1, 3, 7, 9    |   4    |    2.5     |
;;
;; It can be seen that n = 6 produces a maximum n / phi(n) for n <= 10.
;;
;; Find the value of n <= 1000000 for which n / phi(n) is a maximum.
;;

;; Notice that:
;; phi(n) = prod(pi^(ni-1))
;; phi(n * m) = phi(n) * phi(m)
;; phi(p) = p - 1

(defun-cached totient-function (n)
  "Return phi(n). "
  (cond ((= n 1)    1)
        ((primep n) (1- n))
        (t (loop for m from (isqrt n) downto 2
                 if (modp n m)
                   return (* (totient-function m)
                             (totient-function (/ n m)))))))

(defun problem69 (&optional (max 1000000))
  "Find maximum of n / phi(n) for n upto MAX. "
  (loop with nmax = 0
        with vmax = 0
        for n from 1 upto max
        for v = (/ n (totient-function n))
        if (> v vmax)
          do (setf nmax n
                   vmax v)
        finally (return nmax)))


;;; Problem 70. Totient Permutation
;; Euler's totient function, phi(n), is used to determine the number of
;; positive numbers less than or equal to n which are relatively prime
;; to n. For example, as 1, 2, 4, 5, 7, and 8, are all less than nine
;; and relatively prime to nine, phi(9) = 6.
;;
;; The number 1 is considered to be relatively prime to every positive
;; number, so phi(1) = 1.
;;
;; Interestingly, phi(87109) = 79180, and it can be seen that 87109
;; is a permutation of 79180.
;;
;; Find the value of n, 1 < n < 10^7, for which phi(n) is a permutaion
;; of n and the ratio n / phi(n) produces a minimum.
;;

;; it is slow... (but adding some cache on the totient function,
;; would make it less painful when you redo the problem).

(defun problem70 (&optional (max (expt 10 7)))
  "Find the n that produce maximum n/phi(n) and permutable phi(n). "
  (loop with nmin = 0
        with vmin = -1
        for n from 2 below max
        for phi = (totient-function n)
        for v = (/ n phi)
        if (and (p-digits-permutate-p phi n)
                (or (= -1 vmin) (< v vmin)))
          do (setf vmin v
                   nmin n)
        finally (return nmin)))

;;;; euler100.lisp ends here
