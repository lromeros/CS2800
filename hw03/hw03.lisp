; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
#|

CS 2800 Homework 3 - Fall 2016

This homework is done in groups. The rules are:

 * ALL group members must submit the homework file (this file)
 * the file submitted must be THE SAME for all group members (we use this
   to confirm that alleged group members agree to be members of that group)
 * you must list the names of ALL group members below.

Names of ALL group members: Laura Romero, Khyati Singh

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will need to use ACL2s.

Technical instructions:

- open this file in ACL2s as hw03.lisp

- make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- insert your solutions into this file where indicated (usually as "...")

- only add to the file. Do not remove or comment out anything pre-existing.

- make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- when done, save your file and submit it as hw03.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file.

Instructions for programming problems:

For each function definition, you must provide both contracts and a body.

You must also ALWAYS supply your own tests. This is in addition to the
tests sometimes provided. Make sure you produce sufficiently many new test
cases. This means: cover at least the possible scenarios according to the
data definitions of the involved types. For example, a function taking two
lists should have at least 4 tests: all combinations of each list being
empty and non-empty.

Beyond that, the number of tests should reflect the difficulty of the
function. For very simple ones, the above coverage of the data definition
cases may be sufficient. For complex functions with numerical output, you
want to test whether it produces the correct output on a reasonable
number if inputs.

Use good judgment. For unreasonably few test cases we will deduct points.

We will use ACL2s' check= function for tests. This is a two-argument
function that rejects two inputs that do not evaluate equal. You can think
of check= roughly as defined like this:

(defunc check= (x y)
  :input-contract (equal x y)
  :output-contract (equal (check= x y) t)
  t)

That is, check= only accepts two inputs with equal value. For such inputs, t
(or "pass") is returned. For other inputs, you get an error. If any check=
test in your file does not pass, your file will be rejected.

|#

#|

This time around, we will let ACL2s formally prove the various 
conditions for admitting a function.  Hence ":program" has been
commented out. If you get stuck, you can put things back into
program mode but you will lose a couple points (but better than 0)

NOTE: defdata often doesn't work in program mode.  If you are in
program mode, switch back to logic mode (:logic) and then go
back to program mode.

NOTE 2: Proving function correctness often takes time.  Please be
patient when functions are being admitted.  If they fail,  you'll
see red text output in the REPL window (it won't hang).
|#
;:program

#|

Notes:

1. Testing is cheaper but less powerful than proving. So, by turning off
proving and doing only testing, it is possible that the functions we are
defining cause runtime errors even if called on valid inputs. In the future
we will require functions complete with admission proofs, i.e. without the
above directive. For this homework, the functions are simple enough
that there is a good chance ACL2s's testing will catch any contract or
termination errors you may have.

2. The tests ACL2s runs test only the conditions for admitting the
function. They do not test for "functional correctness", i.e. does the
function do what it is supposed to do? ACL2s has no way of telling what
your function is supposed to do. That is what your own tests are for!

|#

#|
--------------------------------------------------------------------
 Problem I: Basic Programming
 DEFINE, IMPROVE, or FIX the following functions.  
 Improvements should be based on the function's header comments.  
 Fixes should mean the function can be admitted into ACL2s (yet still 
 conform to the description of the function.....no putting t as the 
 output contract or removing important function calls)
 New functions require removing the "..."s but will not require you to write
 input and output contracts.
 --------------------------------------------------------------------
|#

;; Leave this code alone:  It changes when ACL2s gives up on proving termination.
(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(set-defunc-timeout 80)
(acl2s-defaults :set cgen-timeout 2)


(defdata lor (listof rational))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FIX
;; sortedp: LOR -> booleanp
;; This is a special recognizer since it only takes lists of rationals (l)
;; and returns true iff the list is sorted.
;; Edit the function so that it works.

(defunc sortedp (l)
  :input-contract (lorp l)
  :output-contract (booleanp (sortedp l))
  (if (endp l)
    t
    (if (equal (len l) 1)
      t
      (if (<= (first l)(first (rest l)))
          (sortedp (rest l))
          nil))))
     
(defconst *l2* (list -1 -1))
(defconst *v* -1/2)
(check= (endp *l2*) nil)
(check= (< *v* (first *l2*)) nil)
(check= (cons (first *l2*) (list *v*)) (list -1 *v*))
(check= (append (list (first *l2*)) (list *v*)) (list -1 *v*))
(check= (cons -1/2 nil) (list -1/2))
(check= (cons -1 (cons -1/2 nil))(list -1 -1/2))
(check= (cons -1 (list -1 -1/2))(list -1 -1 -1/2))
(check= (sortedp (list -1 -1 -1/2))t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Improve
;; insert: rational x lor -> lor
;; (insert val l) takes a rational val and a list of rationals l and 
;; returns the list with val inserted in the "correct" spot such
;; that elements before val are <= val and elements after val are greater.
;; What do we want to say about l before and after insert is called? Put
;; those conditions in the contracts.
(defunc insert (val l)
  :input-contract (and (lorp l)(rationalp val))
  :output-contract (and (equal (+ 1 (len l))(len (insert val l)))
                    (lorp (insert val l)))
  (cond ((endp l)          (cons val nil))
        ((< val (first l)) (cons val l))
        (t                 (cons (first l)(insert val (rest l))))))

(defconst *l1* (list 3 1 5))
(check= (sortedp *l1*) nil)
(check= (< (first *l1*)(first (rest *l1*))) nil)
(defconst *list2* (list 4 5 8 9))
(check= (sortedp *list2*) t)
(check= (> (first *l2*)(first (rest *l2*))) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; isort: lor -> lor
;;
;; (isort l) takes a list of rational numbers l
;; returns a sorted list with the same elements.
;; Sorting is done using the insertion sort algorithm
;; (hence isort)

(defunc isort (l)
  :input-contract (lorp l)
  :output-contract (and (lorp (isort l))(or (sortedp (isort l)) nil))
  (if (endp l)
      nil
      (insert (first l)(isort (rest l)))))
  
;; Add tests for isort and insert including a minimum
;; of one test?
(check= (insert 3/2 '()) '(3/2))
(check= (insert 0 '(1 2 6 7)) '(0 1 2 6 7))
(check= (isort '()) nil)
(check= (isort '(9 8 4 5 7)) '(4 5 7 8 9))
(check= (isort '(2 8 4 0 7 8 11)) '(0 2 4 7 8 8 11)) 

(test? (implies (endp l) 
                (equal (isort l)
                       nil)))
                          
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;;
;; top-n-values: lor x nat -> lor
;; (top-n-values l n) takes a list of rational numbers l
;; and a natural number n and returns a list of the n largest numbers in l
(defunc top-n-values (l n)
  :input-contract (and (lorp l)(natp n))
  :output-contract (lorp (top-n-values l n))
  (if (< (len l) n)
    (isort l)
    (if (sortedp l)
      (if (equal n (len l))
        l
        (top-n-values (rest l) n))
      (top-n-values (isort l) n))))

(check= (top-n-values '(1 2 3 4 5 6 7) 5) '(3 4 5 6 7))
(check= (top-n-values '(1 2 3 4 5 6 7) 17) '(1 2 3 4 5 6 7))
;; Write additional tests as determined by the data
(check= (top-n-values '() 1) nil)
(check= (top-n-values '(8 7 3 4 0 9 2) 3) '(7 8 9))
(check= (top-n-values '(7 4 3 0 0 1) 200) '(0 0 1 3 4 7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Predefined functions to save you time (Start)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; I will define a number of functions to simplify your life
;; ....and so you won't have to figure out how to make round, rem or nat/ 
;; work in logic mode. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; rem-similar: Nat x Nat-{0} -> Nat
;
; (rem-similar x y) returns the remainder of the integer division of 
; x by y assuming that x and y are relatively the same size.
; This is a helper method for (rem x y)
(defunc rem-similar (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (rem-similar x y))
  (if (< x y)
    x
    (if (equal y 1)
      0
      (rem-similar (- x y) y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; rem-smally: Nat x Nat-{0} -> Nat
;
; (rem-smally x y) returns the remainder of the integer division of 
; x by y assuming that y is relatively small compared to x.
; This is a helper method for (rem x y)
(defunc rem-smally (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (rem-smally x y))
  (if (< x y)
    x
    (if (integerp (/ x y))
      0
      (+ 1 (rem-smally (- x 1) y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; rem: Nat x Nat-{0} -> Nat
;
; (rem x y) returns the remainder of the integer division of x by y.
; For x and y being approximately the same size we use (rem-similar)
; since it is more efficient.
; For small values of y (and arbitrarily large x values), rem-smally
; is used.
(defunc rem (x y)
  :input-contract (and (natp x)(posp y))
  :output-contract (natp (rem x y))
  (if (< y (/ x y))
    (rem-smally x y)
    (rem-similar x y)))
  
(check= (rem 2 4) 2)
(check= (rem 4 2) 0)
(check= (rem 16 1) 0)
(check= (rem 1234567 10) 7)
(check= (rem 123 48) 27)

; Additional Checks
(check= (rem 1 16) 1)
(check= (rem 0 1) 0)
(check= (rem 2999 11) 7)
(check= (rem 1234567 93) 85)
(check= (rem 12345677 48777) 5096)
(test? (implies (and (natp x)(posp y)) 
                (equal (rem-smally x y)(rem-similar x y))))

;; Extra Theorems used to prove nat/ works as expected.
(defthm rem-mag-similar (implies (and (natp x)(posp y))
                         (<= (rem-similar x y) x)))
(defthm rem-mag-small (implies (and (natp x)(posp y))
                         (<= (rem-smally x y) x)))
(defthm rem-mag (implies (and (natp x)(posp y))
                         (<= (rem x y) x)))
(defthm nat-rem-small (implies (and (natp x)(posp y))
                               (natp (/ (- x (rem-smally x y)) y))))
(defthm nat-rem-similar (implies (and (natp x)(posp y))
                               (natp (/ (- x (rem-similar x y)) y))))

(defunc nat-/-similar (x y)
  :input-contract (and (natp x) (posp y))
  :output-contract (natp (nat-/-similar x y))
  (/ (- x (rem-similar x y)) y))

(defunc nat-/-smally (x y)
  :input-contract (and (natp x) (posp y))
  :output-contract (natp (nat-/-smally x y))
  (/ (- x (rem-smally x y)) y))

(defthm thm-nat-nat/ (implies (and (natp x)(posp y))
                              (natp (if (< y (/ x y))
                                      (nat-/-similar x y)
                                      (nat-/-smally x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; nat/: Nat x Nat-{0} -> Nat
;;
;; (nat/ x y) returns the result of integer division of x by y.
;; That is, it returns the integer part of x/y (so 7/3 = 2),
;; which is a natural number. See the examples below.
;; NOTE: to get this through the prover, I cheated and didn't go through function
;; rem
(defunc nat/ (x y)
  :input-contract (and (natp x) (posp y))
  :output-contract (integerp (nat/ x y))
  (if (< y (/ x y))
    (nat-/-smally x y)
    (nat-/-similar x y)))

(check= (nat/ 10 2) 5)
(check= (nat/ 11 2) 5)

; Additional Checks
(check= (nat/ 1 1) 1)
(check= (nat/ 2 1) 2)
(check= (nat/ 5 2) 2)
(test? (implies (and (natp x) (posp y)) (equal (+ (rem x y) (* (nat/ x y) y)) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; abs: Rationalp -> Rationalp >= 0
;; (abs r) calculates the absolute value of a rational number r
(defunc abs (r)
  :input-contract (rationalp r)
  :output-contract (and (rationalp (abs r))(>= (abs r) 0)) 
  (if (< r 0)
    (unary-- r)
    r))

(check= (abs -3/2) 3/2)
(check= (abs 3/2) 3/2)
(check= (abs -3456778/2) 3456778/2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; floor: Rational -> Integer
;;
;; (floor r) returns the closest integer less than rational r 
;; (if r is an integer return r).
(defunc floor (r)
  :input-contract (rationalp r)
  :output-contract (integerp (floor r))
  (let* ((absnum (abs (numerator r)))
         (denom (denominator r))
         (posfloor (nat/ absnum denom)))
    (cond ((integerp r)   r)
          ((< (numerator r) 0)         (- (unary-- posfloor) 1))
          (t                           posfloor))))


(check= (floor 4/3) 1)
(check= (floor 3/4) 0)
(check= (floor 2) 2)
(check= (floor -2) -2)
(check= (floor -4/3) -2)
(check= (floor 0) 0)
(check= (floor 24/5) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; round: Rational -> Integer
;;
;; (round r) takes a rational number r and rounds it up or 
;; down depending on the value.  
(defunc round (r)
  :input-contract (rationalp r)
  :output-contract (integerp (round r))
  (let ((floorval (floor r)))
    (if (equal r floorval)
      r
      (if (< 1/2 (- r floorval))
        (+ floorval 1)
        floorval))))

(check= (round 4/3) 1)
(check= (round 3/4) 1)

;; Additional Checks
(check= (round 2) 2)
(check= (round -2) -2)
(check= (round -4/3) -1)
(check= (round -5/3) -2)
(check= (round 0) 0)
(check= (round 24/5) 5)
(check= (round 1/3) 0)
(check= (round 28/3) 9) 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Predefined functions to save you time (END)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FIX the input contract (including this comment)
;; ith-rational: LOR (first element is 0) x Integer -> Rational
;;
;; (ith-rational l i) takes a list or rationals l and an index i
;; and returns the list element at position i (the first element
;; is element 0).
;; This function should not work for invalid input.
(defunc ith-rational (l i)
  :input-contract (and (lorp l)
                   (or (natp i)(equal i 0))
                   (< i (len l)))
  :output-contract (rationalp (ith-rational l i))
  (if (equal i 0)
    (first l)
    (ith-rational (rest l) (- i 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; median: lor (not empty) -> rational
;; (median l) take a list of rational numbers and returns
;; the number with half of l being smaller or equal and the other half being larger
;; or equal.
;; Odd sized lists should return the (floor (len/2))th smallest element.
;; Even sized lists should return element len/2
(defunc median (l)
  :input-contract (and (lorp l)(not (endp l)))
  :output-contract (rationalp (median l))
  (if (equal (len l) 1)
    (ith-rational l 0)
    (ith-rational (isort l) (floor (/ (len l) 2)))))

(check= (median '(1 2 3 4 5)) 3)
(check= (median '(5 2 4 3 1)) 3)
(check= (median '(3 1 2 4)) 3)
;; Add your own tests here.
(check= (median '(7 4 0 9)) 7) 
(check= (median '(11 5 8 6 20)) 8)
(test? (implies (equal (len l) 1)
                (equal (median l)
                       (first l))))
#|
--------------------------------------------------------------------
 Problem II: A Return to the Precision Problem
 Now that we have data definitions we can generate
 strings that show the decimal format of a rational number
 (precision must be limited to a set number of positions)
 
 First, you need to write several data definitions based on the description comment
 ---------------------------------------------------------------------
|#

;; Given that we need to convert a rational to a "decimal" number,
;; we need a hard lower limit on the number of decimal places
;; otherwise numbers like 1/3 wouldn't work.  *min-lsp* stands
;; for minimum least significant position and effectively means
;; we can store up to 6 positions smaller than the decimal point.
(defconst *min-lsp* -6)
(defconst *dec-shifter* 1000000)

;; Define an enumerated data definition "digit" consisting of characters #\0 through #\9
;; #\- and \#. ....I realize that - and . are technically not digits but please
;; ignore this point.
(defdata digit (enum '(#\- #\. #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)))

;; Define a list of digits which can represent a number.
(defdata lodigit (listof digit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IMPROVE
;; zeronine-to-digit
;; Helper function for int-to-digit where a single
;; value d between 0 and 9 is mapped to an element in
;; the digit data type. You must STRENGTHEN the input
;; contract and output
(defunc zeronine-to-digit(d)
  :input-contract (and (natp d)
                       (<= 0 d)
                       (<= d 9))
  :output-contract (digitp (zeronine-to-digit d))
  (cond ((equal d 0) #\0)
        ((equal d 1) #\1)
        ((equal d 2) #\2)
        ((equal d 3) #\3)
        ((equal d 4) #\4)
        ((equal d 5) #\5)
        ((equal d 6) #\6)
        ((equal d 7) #\7)
        ((equal d 8) #\8)
        (t           #\9)))
(cons (list 4)(list 9))
(append (list 4)(list 9))
(append (append (list 4)(list 9))(list 2))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; int-to-digits: Integer -> List of Digits
;; 
;; int-to-digits is a helper method to rat-to-decimal
;; that takes an integer and creates a string of characters
;; representing that number. 
(defunc int-to-digits (i)
  :input-contract (integerp i)
  :output-contract (lodigitp (int-to-digits i))
  (if (< i 0)
    (cons #\- (int-to-digits (abs i)))
    (if (< i 10)
      (list (zeronine-to-digit i))
      (append (int-to-digits (floor (/ i 10)))
              (list (zeronine-to-digit (rem i 10)))))))

(check= (int-to-digits 14) '(#\1 #\4))
(check= (int-to-digits -14) '(#\- #\1 #\4))
;; Add additional tests
(check= (int-to-digits -2893) '(#\- #\2 #\8 #\9 #\3))
(check= (int-to-digits 0) '(#\0))
(check= (int-to-digits 187) '(#\1 #\8 #\7))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; clip-rational: Rational -> Integer 
;;
;; (clip-rational r) takes a rational number and
;; returns only the integer component of the number
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defunc clip-rational (r)
  :input-contract (rationalp r)
  :output-contract (integerp (clip-rational r))
  (if (< r 0)
    (+ (floor r) 1)
    (floor r)))

;; Add your tests here
(check= (clip-rational -3/4) 0)
(check= (clip-rational 3/4) 0)
(check= (clip-rational -4/3) -1)
(check= (clip-rational 4/3) 1)
(check= (clip-rational 4) 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; IMPROVE
;; decimal-values: Rational -> Integer
;;
;; decimal-value takes a rational number r
;; (that is expected to have an absolute value less than 1 but
;; that doesn't have to be part of the IC) and
;; returns an integer representing the decimal representation
;; of r up to 6 decimal places (based on *dec-shifter*)
;; Helper function of rational-to-decstring.
;; TODO: modify this function from HW2 to remove least
;; significant bit zeros (so 0.2222 becomes 2222 rather
;; than 222200 while 0.333333 remains the same)
(defunc decimal-values (r)
  :input-contract (rationalp r)
  :output-contract (integerp (decimal-values r))
  (cond 
   ((equal r 0) 0)
   ((< r 0) (decimal-values (abs r)))
   (t (if (integerp r)
        (if (equal (rem (clip-rational (abs r)) 10) 0)
          (decimal-values (/ r 10))
          r)
        (if (equal (rem (clip-rational (* (abs r) *dec-shifter*)) 10) 0)
          (decimal-values (/ r 10))
          (clip-rational (* (abs r) *dec-shifter*)))))))

(check= (decimal-values 0) 0)
(check= (decimal-values 3/4) 75)
(check= (decimal-values 4/5) 8)
(check= (decimal-values -2/3) 666666)

(test? (implies (rationalp r)
                (lodigitp (int-to-digits (clip-rational (abs r))))))
(check= (clip-rational 15/4) 3)
(check= (int-to-digits 3) '(#\3))
(check= (- 15/4 (floor 15/4)) 3/4)
(check= (int-to-digits 75) '(#\7 #\5))
(append (list '(#\3) #\.)
        (list #\7 #\5))
(append (append (int-to-digits (clip-rational 4/3)) '(#\.))
              (int-to-digits (decimal-values (- 4/3 (floor 4/3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define 
;; rational-to-declist (r): Rational -> List of Digits
;;
;; Takes a rational number r and returns a list of digits representation
;; of that number.  Note: helper functions from the last assignment
;; have been provided for you.
(defunc rational-to-declist (r)
  :input-contract (rationalp r)
  :output-contract (lodigitp (rational-to-declist r))
  (if (equal 0 r)
    (list #\0)
    (if (< r 0)
      (cons #\- (rational-to-declist (abs r)))
      (if (< r 1)
        (append (list #\0 #\.)
                (int-to-digits (decimal-values r)))
        (if (integerp r)
          (int-to-digits r)
          (append (append (int-to-digits (clip-rational r)) '(#\.))
                  (int-to-digits (decimal-values (- r (floor r))))))))))

(check= (rational-to-declist 1/3) '(#\0 #\. #\3 #\3 #\3 #\3 #\3 #\3))
(check= (rational-to-declist -1/3) '(#\- #\0 #\. #\3 #\3 #\3 #\3 #\3 #\3))
;; Note: since the precision is not being set, the digits are clipped not rounded.
(check= (rational-to-declist -5/3) '(#\- #\1 #\. #\6 #\6 #\6 #\6 #\6 #\6))
(check= (rational-to-declist 0) '(#\0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rat-as-decstring: Rational -> String
;;
;; rat-as-decstring converts a rational number into a decimal
;; format string. This will let you test your set-precision method
;; better. This function was provided so you don't have to worry 
;; about ACL2s nuances.
(defunc rat-as-decstring (r)
  :input-contract (rationalp r)
  :output-contract (acl2::stringp (rat-as-decstring r))
  (acl2::coerce (rational-to-declist r) 'string))

(check= (rat-as-decstring 1/3) "0.333333")
;; Again, values are clipped rather than rounded
(check= (rat-as-decstring -2/3) "-0.666666")
(check= (rat-as-decstring 0) "0")
(check= (rat-as-decstring 47/3) "15.666666")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; set-precision: Rational x Integer -> Rational
;;
;; Returns the value of r altered to set the precision 
;; indicated by integer dig. Dig can be considered the least 
;; significant power of 10 position in r (like in 
;; scientific notation) that is not 0. 
;; Thus (set-precision 1234/100 1) returns 10,
;; (set-precision 1234/100 -1) returns 12.3
;; and (set-precision 1234/100 0) returns 12.
;; See the check= tests for other examples.
(defunc set-precision (r dig)
  :input-contract (and (rationalp r)(integerp dig)(>= dig *min-lsp*))
  :output-contract (rationalp (set-precision r dig))
  (cond ((< dig 0) (/ (set-precision (* r 10) (+ dig 1)) 10))
        ((> dig 0) (* (set-precision (/ r 10) (- dig 1)) 10))
        (t         (round r))))
(check= (set-precision 1234/100 1) 10)
(check= (set-precision 1234/100 0) 12)
(check= (set-precision 1234/100 -1) 123/10)
(check= (set-precision -22/20 0) -1)

;;; EXTRA CHECKS
(check= (set-precision -1/3 -2) -33/100)
(check= (set-precision -1/3 -4) -3333/10000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now test that set-precision works as expected by 
;; seeing how the string representation of the number changes
(check= (rat-as-decstring (* -1/3 1000)) "-333.333333")
(check= (rat-as-decstring (set-precision (* -1/3 1000) 1)) 
        "-330")
(check= (rat-as-decstring (set-precision (* -1/3 1000) 2)) 
        "-300")
(check= (rat-as-decstring (set-precision (* -1/3 1000) 3)) 
        "0")
;; Add Additional Tests
(check= (rat-as-decstring (set-precision (* 1/2 100000) 0))
        "50000")
(check= (rat-as-decstring (set-precision (* -1/2 100) 1))
        "-50")
(check= (rat-as-decstring (set-precision (* 229/100 10000) 3))
        "23000")
#|
--------------------------------------------------------------------
;; Problem III
;; Student Grade Data Definitions
;;
;; Soon I will be asking you to write a program which determines
;; your mark in the course (given that BB stinks for handling
;; dropped grades)
;; However, first I want to define how we can store these data 
;; (FYI: data is the plural of datum)
;; Each grade will be a record storing student ID, section, grade type, 
;; exam/hw/quiz number, and the grade.
;; Each grade will be a score and a maximum score.
;;
;; For example HW02 for John Smith (ID: 123456) in section 2 could take the form:
;; (grade-rec 123456 'section2 'assignment 2 (list 80 100))
--------------------------------------------------------------------
|#

;; First define an enumerated datatype for the kind of evaluation (exam, assignment or quiz).
(defdata grade-type (enum '(exam assignment quiz)))
(check= (grade-typep 'exam) t)
(check= (grade-typep 'assign) nil)
(check= (grade-typep 'assignment) t)

;; Define the two sections using an enumerated list of symbols (rather than a number)
(defdata section-number (enum '(section1 section2)))
(check= (section-numberp 'section2) t)
(check= (section-numberp 'section1) t)
(check= (section-numberp 'section3) nil)

;; Student IDs consist of positive numbers 6 to 10 digits long. 
;; Define the permitted range
(defdata studentID (range integer (111111 <= _ <= 9999999999)))
(check= (studentIDp 983451173) t)
(check= (studentIDp 100) nil)
(check= (studentIDp 99999999999) nil)
(check= (studentIDp 1234567) t)

;; Student marks are exclusively between 0 and 100 but can include part marks.
;; Make a data definition to represent valid student grades.
(defdata grade (range rational (0 <= _ <= 100)))
(check= (gradep 67) t)
(check= (gradep 834/10) t)
(check= (gradep 0) t)
(check= (gradep 100) t)
(check= (gradep 1/1000000) t)
(check= (gradep 99999/100000) t)
(check= (gradep 834345/10000) t)
(check= (gradep 85) t)

;; Define the set of maximum grades that are permitted (24 for quizzes or 100 otherwise)
(defdata grade-max (oneof 24 100))
(check= (grade-maxp 24) t)
(check= (grade-maxp 100) t)
(check= (grade-maxp 23) nil)
(check= (grade-maxp 101) nil)
(check= (grade-maxp 49) nil)
                       
;; Make a data definition called grade-score which is a grade range and max grade list.
;; representing what a student got and the best possible mark. 
;; Percentages can be calculated from this.
(defdata grade-score (list grade grade-max))
                      
(check= (first (list 18 24)) 18)
(check= (second (list 18 24)) 24)
(check= (grade-scorep (list 18 24)) t)
(check= (grade-scorep (list 85 100)) t)
(check= (grade-scorep (list 85 24)) t)
(check= (grade-scorep (list 18 124)) nil)
(check= (grade-scorep (list 101 100)) nil)
(check= (grade-scorep (list 0 25)) nil)
(check= (grade-scorep (list 1/100000 24)) t)
(check= (grade-scorep (list 100 24)) t)
(check= (grade-scorep (list 100 25)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The grades of each type are numbered, starting from 1. For example, hw02
;; is the assignment grade with number 2. Define a record type that
;; specifies a student id, a grade type, a grade number for that type, and a score.  
;; The field names should be id, section, type, number, and score. 
;; Define this record type:
(defdata grade-rec (record (id . studentID)
                           (section . section-number)
                           (type . grade-type)
                           (number . integer)
                           (score . grade-score)))

(check= (grade-rec-number (grade-rec 1234567 'section1 'assignment 5 (list 85 100))) 5)
(check= (first (grade-rec-score (grade-rec 1234567 'section1 'assignment 5 (list 85 100)))) 85)
(check= (grade-rec-type (grade-rec 1234567 'section1 'assignment 5 (list 85 100))) 'assignment)
(check= (grade-rec-id (grade-rec 1234567 'section1 'assignment 5 (list 85 100))) 1234567)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Finally, the spreadsheet of all grades in the course is a list of grade
;; records.....not truly a spreadsheet but this code addresses the needs Excel
;; would usually address.
(defdata grade-spreadsheet (listof grade-rec))

(check= (grade-spreadsheetp (list (grade-rec 1234567 'section1 'assignment 5 
                                             (list 85 100)))) t)
(check= (grade-recp (first (list (grade-rec 1234567 'section2 'quiz 5 (list 12 24))))) t)
(check= (grade-recp (first (list
                            (grade-rec 1234567 'section1 'assignment 5 (list 85 100))
                            (grade-rec 1234567 'section2 'quiz 5 (list 12 24)) ))) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; To avoid having to keep typing a long list of grade records, it is handy
; to define a global constant which can then be used for many check= tests.
; You should put all of the grades of your team in a spreadsheet. Use your
; group name for the name of this spreadsheet. Your spreadsheet should
; contain your actual grades, but do not use your actual NEU ids as your
; student ids. Your check= tests should use your own spreadsheet.
; Here is a modifiable example.
; NOTE: as a corollary, I expect that you will be able to calculate
; your own final grades at the end of term.  Please don't ask how
; to do this in late November. :-)
(defconst *cs2800* (list (grade-rec 1234567 'section1 'assignment 5 (list 85 100))
                         (grade-rec 1234567 'section1 'quiz 4 (list 18 24))
                         (grade-rec 1234567 'section1 'quiz 3 (list 12 24))
                         (grade-rec 55555555 'section2 'assignment 4 (list 75 100))
                         (grade-rec 55555555 'section2 'quiz 2 (list 12 24))
                         (grade-rec 55555555 'section2 'quiz 1 (list 24 24))))

(check= (first (grade-rec-score (first (rest *cs2800*)))) 18)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part IV: Calculating your average
;; Since each person gets the same number of dropped assignments, 
;; quizzes, and exams we define the number of COUNTED grades for 
;; each type as constants (change as your number of marks grows)
(defconst *num-assignments* 10)
(defconst *num-exams* 2)
(defconst *num-quizzes* 20)

(defconst *pct-assignments* 20)
(defconst *pct-quizzes* 20)
(defconst *pct-exams* 60)

;; Define a list of grade-scores so you can extract the set of marks to average.
(defdata score-list (listof grade-score))
(defconst *sl1* (list (list 18 24)(list 85 100)
                      (list 8 24)(list 18 100)))
(check= (score-listp *sl1*) t)
(check= (score-listp '()) t)
(check= (score-listp (list 18 24)) nil)
(check= (score-listp (list (list 18 24))) t)
(check= (score-listp (list (list 50 24))) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; student-marks-list: grade-spreadsheet x studentID -> grade-spreadsheet
;;
;; (student-marks-list l sn)
;; From a list of grade record scores (l), extract all entries
;; associated with a given student number (sn)
(defunc student-marks-list (l sn)
  :input-contract (and (grade-spreadsheetp l) (studentIDp sn))
  :output-contract (grade-spreadsheetp (student-marks-list l sn))
  (if (endp l)
    nil
    (if (equal (grade-rec-id (first l)) sn)
      (cons (first l) (student-marks-list (rest l) sn))
      (student-marks-list (rest l) sn))))

;; TO BE MODIFIED based on your data
(check= (student-marks-list *cs2800* 55555555)
        (list (grade-rec 55555555 'section2 'assignment 4 (list 75 100))
              (grade-rec 55555555 'section2 'quiz 2 (list 12 24))
              (grade-rec 55555555 'section2 'quiz 1 (list 24 24))))
(check= (student-marks-list '() 55555555) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; type-scores-list: grade-spreadsheet x grade-type -> score-list
;; (type-scores-list l type) takes a grade-spreadsheet plus a grade type 
;; and returns all scores associated with that grade type.
(defunc type-scores-list (l type)
  :input-contract (and (grade-spreadsheetp l) (grade-typep type))
  :output-contract (score-listp (type-scores-list l type))
  (if (endp l)
    nil
    (if (equal (grade-rec-type (first l)) type)
      (cons (cons (first (grade-rec-score (first l)))
                  (rest (grade-rec-score (first l))))
            (type-scores-list (rest l) type))
      (type-scores-list (rest l) type))))

 ;; Add your own tests here.
(check= (type-scores-list *cs2800* 'assignment) (list (list 85 100)
                                                      (list 75 100)))
(check= (type-scores-list nil 'assignment) nil)
(test? (implies (endp l)
                (equal (type-scores-list l type) nil)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; student-scores-list: grade-spreadsheet x studentID x grade-type -> score-list
;;
;; (student-scores-list l sn type) takes a grade-spreadsheet l a 
;; student number/ID (sn) and a grade type (type) 
;; and returns the list of scores for that student and that 
;; grade type. 
(defunc student-scores-list (l sn type)
  :input-contract (and (grade-spreadsheetp l)(studentIDp sn) (grade-typep type))
  :output-contract (score-listp (student-scores-list l sn type))
  (if (endp l)
    nil 
    (if (and (equal (grade-rec-id (first l)) sn)
             (equal (grade-rec-type (first l)) type))
      (cons (cons (first (grade-rec-score (first l)))
                  (rest (grade-rec-score (first l))))
            (student-scores-list (rest l) sn type))             
      (student-scores-list (rest l) sn type))))

;; Add your own tests here.
(check= (student-scores-list *cs2800* 55555555 'assignment) (list (list 75 100)))
(check= (student-scores-list nil 55555555 'assignment) nil)
(test? (implies (endp l)
                (equal (student-scores-list l sn type) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper
;; calc-individual: grade-score -> rational
;; (calc-individual gs) takes a grade-score gs and returns a 
;; rational number representing the score of that assignment
;; divides gs' grade by gs' grade-max
(defunc calc-individual (gs)
  :input-contract (grade-scorep gs)
  :output-contract (rationalp (calc-individual gs))
  (/ (first gs) (second gs)))

(check= (calc-individual (list 12 24)) 1/2)
(check= (calc-individual (list 40 100)) 4/10)
(check= (calc-individual (list 1 100)) 1/100)
(check= (calc-individual (list 1 24)) 1/24)
(check= (calc-individual (list 24 100)) 24/100)
(check= (calc-individual (list 48 24)) 2)

;; -----------------------------------------------------------
;; Helper
;; all-indiv-scores: score-list -> list
;; (all-indiv-scores sl) takes a score-list sl 
;; and returns a sorted list of individual assignment grades
(defunc all-indiv-scores (sl)
  :input-contract (score-listp sl)
  :output-contract (listp (all-indiv-scores sl))
  (if (endp sl)
    nil
    (cons (calc-individual (first sl))
          (all-indiv-scores (rest sl)))))

(check= (all-indiv-scores *sl1*)
        (list 3/4 17/20 1/3 9/50)) 
(check= (lorp (all-indiv-scores *sl1*)) t)
(test? (implies (endp l)
                (equal (all-indiv-scores sl) nil)))
;; -----------------------------------------------------------
;; Helper
;; only-counted-scores: score-list x pos-> list
;; (only-counted-scores sl n) takes a score-list sl 
;; and returns a sorted list of length n individual 
;; assignment grades
(defunc only-counted-scores (sl n)
  :input-contract (and (score-listp sl)(posp n))
  :output-contract (and (sortedp (only-counted-scores sl n))
                        (equal (len (only-counted-scores sl n)) n))
  (if (<= n (len sl))
       (top-n-values (isort (all-indiv-scores sl)) n)
       (only-counted-scores (cons (list 0 24) sl) n)))

(check= (only-counted-scores *sl1* 1)
        (list 17/20))
(check= (only-counted-scores *sl1* 2)
        (list 3/4 17/20))
(check= (only-counted-scores *sl1* 4)
        (list 9/50 1/3 3/4 17/20))
(check= (only-counted-scores *sl1* 6)
        (list 0 0 9/50 1/3 3/4 17/20))
(check= (only-counted-scores nil 2)
        (list 0 0))


;; -----------------------------------------------------------
;; Helper
;; add-indiv-scores: score-list n -> rational
;; (add-indiv-scores sl n) takes a score-list sl 
;; and returns the sum of all the rationals in sl
(defunc add-indiv-scores (l)
  :input-contract (lorp l)
  :output-contract (rationalp (add-indiv-scores l))
  (if (endp l)
    0
    (+ (first l)
       (add-indiv-scores (rest l)))))
(check= (add-indiv-scores (only-counted-scores *sl1* 5)) 317/150)
(check= (add-indiv-scores '()) 0)
(test? (implies (and (endp l)(lorp l))
                (equal (add-indiv-scores l) 0)))
;; -----------------------------------------------------------
;; Define
;; calc-mark: score-list x pos x nat -> rational
;; (calc-mark sl n val) takes a score-list sl 
;; and based on the number of scores counted (n)
;; and how much the grades are worth as an integerp percent
;; (val), the total percent value for those scores is returned.
;; Helper methods are strongly encouraged
(defunc calc-mark (sl n val)
  :input-contract (and (score-listp sl)(posp n)
                       (natp val)(<= (len sl) n))
  :output-contract (rationalp (calc-mark sl n val))
  (if (endp sl)
    0
    (* (add-indiv-scores (only-counted-scores sl n)) val)))
;; tests
(defconst *sl2* (list (list 24 24)(list 24 24) 
      (list 24 24)(list 24 24)
      (list 24 24)(list 24 24)
      (list 24 24)(list 24 24)
      (list 24 24)(list 24 24)))
(check= (calc-mark *sl2* 10 4) 40)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; calc-grade: grade-spradsheet x studentID -> rational
;; (calc-grade l sn) takes a grade spreadsheet l 
;; and a student number sn then extracts all records 
;; for that student and for each assignment type 
;; calculates the mark to be given.  Summing the results from 
;; each calc-mark call should give the final percent in the course.
(defunc calc-grade (l sn)
  :input-contract (and (grade-spreadsheetp l)
                       (studentIDp sn))
  :output-contract (rationalp (calc-grade l sn))
  (if (endp l)
    0
    (+ (if (endp (student-scores-list l sn 'exam))
         0
         (/ (calc-mark (student-scores-list l sn 'exam)
              (len (student-scores-list l sn 'exam))
              *pct-exams*) *num-exams*))
       (+ (if (endp (student-scores-list l sn 'quiz))
            0
            (/ (calc-mark (student-scores-list l sn 'quiz)
                          (len (student-scores-list l sn 'quiz))
                          *pct-quizzes*) *num-quizzes*))
          (if (endp (student-scores-list l sn 'assignment))
            0
            (/ (calc-mark (student-scores-list l sn 'assignment)
                          (len (student-scores-list l sn 'assignment))
                          *pct-assignments*) *num-assignments*))))))

;; Another set of marks to test your code against.
(defconst *cs2800-Test* (list (grade-rec 1234567 'section1 'quiz 22 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 21 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 20 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 19 (list 0 24))
                              (grade-rec 1234567 'section1 'quiz 18 (list 0 24))
                              (grade-rec 1234567 'section1 'quiz 17 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 16 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 15 (list 24 24))
                              (grade-rec 1234567 'section1 'quiz 14 (list 24 24))
                              (grade-rec 1234567 'section1 'quiz 13 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 12 (list 12 24))
                              (grade-rec 1234567 'section1 'quiz 11 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 10 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 9 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 8 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 7 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 6 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 5 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 4 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 3 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 2 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 1 (list 12 24))
                              (grade-rec 1234567 'section1 'assignment 11 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 10 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 9 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 8 (list 0 100))
                              (grade-rec 1234567 'section1 'assignment 7 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 6 (list 65 100))
                              (grade-rec 1234567 'section1 'assignment 5 (list 55 100))
                              (grade-rec 1234567 'section1 'assignment 4 (list 85 100))
                              (grade-rec 1234567 'section1 'assignment 3 (list 95 100))
                              (grade-rec 1234567 'section1 'assignment 2 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 1 (list 75 100))
                              (grade-rec 1234567 'section1 'exam 2 (list 65 100))
                              (grade-rec 1234567 'section1 'exam 1 (list 65 100))
                              (grade-rec 55555555 'section2 'quiz 2 (list 12 24))
                              (grade-rec 55555555 'section2 'assignment 4 (list 75 100))
                              (grade-rec 55555555 'section2 'quiz 3 (list 12 24))
                              (grade-rec 55555555 'section2 'quiz 4 (list 24 24))
                              (grade-rec 55555555 'section2 'quiz 1 (list 24 24))))

(check= (calc-grade *cs2800-Test* 1234567) (+ (* 20 18/24)
                                              (+ (* 20 75/100) 
                                                 (* 60 65/100))))

;;  Add additional tests based on your spreadsheet.
;; Another set of marks to test your code against.
(defconst *big-example* (list (grade-rec 1234567 'section1 'quiz 22 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 21 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 20 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 19 (list 0 24))
                              (grade-rec 1234567 'section1 'quiz 18 (list 0 24))
                              (grade-rec 1234567 'section1 'quiz 17 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 16 (list 18 24))
                              (grade-rec 1234567 'section1 'quiz 15 (list 24 24))
                              (grade-rec 1234567 'section1 'assignment 11 (list 75 100))
                              (grade-rec 375983 'section1 'assignment 10 (list 75 100))
                              (grade-rec 375983 'section1 'assignment 9 (list 75 100))
                              (grade-rec 375983 'section1 'assignment 8 (list 0 100))
                              (grade-rec 375983 'section1 'assignment 7 (list 75 100))
                              (grade-rec 375983 'section1 'assignment 6 (list 65 100))
                              (grade-rec 375983 'section1 'assignment 5 (list 55 100))
                              (grade-rec 1234567 'section1 'assignment 4 (list 85 100))
                              (grade-rec 1234567 'section1 'assignment 3 (list 95 100))
                              (grade-rec 1234567 'section1 'assignment 2 (list 75 100))
                              (grade-rec 1234567 'section1 'assignment 1 (list 75 100))
                              (grade-rec 1234567 'section1 'exam 2 (list 65 100))
                              (grade-rec 1234567 'section1 'exam 1 (list 65 100))
                              (grade-rec 55555555 'section2 'quiz 2 (list 12 24))
                              (grade-rec 55555555 'section2 'assignment 4 (list 75 100))
                              (grade-rec 55555555 'section2 'quiz 3 (list 12 24))
                              (grade-rec 55555555 'section2 'quiz 4 (list 24 24))
                              (grade-rec 55555555 'section2 'quiz 1 (list 24 24))))
(check= (calc-grade *big-example* 1234567) 1037/20)
(check= (calc-grade *big-example* 375983) 69/10)
(check= (calc-grade *big-example* 55555555) 9/2)#|ACL2s-ToDo-Line|#

