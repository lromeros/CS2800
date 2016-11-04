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
CS 2800 Homework 8 - Fall 2016


This homework is done in groups. The rules are:

 * ALL group members must submit the homework file (this file)

 * The file submitted must be THE SAME for all group members (we
   use this to confirm that alleged group members agree to be
   members of that group)

 * You must list the names of ALL group members below using the
   format below. If you fail to follow instructions, that costs
   us time and it will cost you points, so please read carefully.


Names of ALL group members: Prashan Parvani, Laura Romero-Suarez, Khyati Singh: 

Note: There will be a 10 pt penalty if your names do not follow 
this format.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will need to use ACL2s.

Technical instructions:

- open this file in ACL2s as hw08.lisp

- make sure you are in BEGINNER mode. This is essential! Note that you can
  only change the mode when the session is not running, so set the correct
  mode before starting the session.

- insert your solutions into this file where indicated (usually as "...")

- only add to the file. Do not remove or comment out anything pre-existing
  unless asked to.

- make sure the entire file is accepted by ACL2s. In particular, there must
  be no "..." left in the code. If you don't finish all problems, comment
  the unfinished ones out. Comments should also be used for any English
  text that you may add. This file already contains many comments, so you
  can see what the syntax is.

- when done, save your file and submit it as hw08.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file!

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here are some potentially useful (and admissible) functions.
;; Typical tests and headers are minimal since these aren't for coding. They
;; MAY be useful for measure functions.
;;
;; Throughout the assignment you can also assume abs (below) is defined and returns
;; the absolute value of a rational number.  If the number is an integer, the result
;; is a natural.
;;
;; Finally lists of natural numbers (lon) are defined below for reference
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata lon (listof nat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; max: nat x nat -> nat
;; (max x y) takes two naturals x and y 
;; and returns the larger of the two values.
(defunc max (x y)
  :input-contract (and (natp x)(natp y))
  :output-contract (natp (max x y))
  (if (< x y) y x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; num-branches: Any -> nat
;; (num-branches x) counts the number of "branches" in x 
;; which determines both the number of sub-atoms in x 
;; (0 indictates x is an atom) and the depth of each such atom.
(defunc num-branches (x)
  :input-contract t
  :output-contract (natp (num-branches x))
  (if (atom x)
    0
    (+ (+ 1 (num-branches (first x))) 
       (+ 1 (num-branches (rest x))))))
    
(check= (num-branches '(1 ((2 4 (5 2))) (2 (3 4)))) 26)
(check= (num-branches nil) 0)
(check= (num-branches '(1 (2))) 6)
(thm (implies (listp l) (equal (num-branches (cons l nil)) 
                                 (+ 2 (num-branches l)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; max-depth: Any -> Nat
;; (max-depth x) returns the maximum depth of an
;; element x.  Atoms are value 0. Flat lists have
;; depth 1.  Lists with sub-lists return > 1.
(defunc max-depth (x)
  :input-contract t
  :output-contract (natp (max-depth x))
  (if (atom x)
    0
    (max (+ 1 (max-depth (first x)))
         (max-depth (rest x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abs: rational -> rational (> 0)
;; (abs r) takes a rational r and returns the magnitude
;; of r (or how far r is from 0)
(defunc abs (r)
  :input-contract (rationalp r)
  :output-contract (and (rationalp (abs r)) (>= (abs r) 0))
  (if (< r 0)
    (unary-- r)
    r))#|ACL2s-ToDo-Line|#

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
FUNCTION WITH THE GIVEN PROOF OBLIGATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
For each one of questions 1-3, you are given the proof obligations 
corresponding to condition 4 (from hw07) that a measure function must 
satisfy (the natural number decreases with each recursive call). 
1) Come up with (terminating) functions f1, f2, f3 that give rise to the given obligations 
corresponding to condition 4. 
m1, m2, m3 are measure functions for f1, f2, f3, respectively. 
2) Write the definitions of suitable measure functions m1, m2, m3

For example:
(implies (and (posp p)(> p 1))
         (< (m0 (- p 1)) (m0 p))
         
(defunc f0 (x)
 :input-contract (posp p)
 :output-contract (posp (f0 x))
 (if (> p 1)
     (f0 (- p 1))
     p))
     
(defunc m0 (x)
 :input-contract (posp p)
 :output-contract (natp (m0 x))
 x)
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
1. 
(implies (and (listp x) (natp n) (not (endp x)))
         (< (m1 (rest x) n) (m1 x n)))
         
(defunc f1 (x n)
 :input-contract (and (listp x) (natp n))
 :output-contract (listp (f1 x n))
 (if (endp x)
     x
     (if (equal (first x) n)
         (cons (first x)(f1 (rest x) n)))))
         
(defunc m1 (x n)
 :input-contract (and (listp x) (natp n))
 :output-contract (natp (m1 x n))
 (len x))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
2.
For first recursive call:
(implies (and (natp n) (integerp i) (not (equal i 0)) (< i 0))
         (< (m2 n (+ i 1)) (m2 n i)))
         
For second recursive call:
(implies (and (natp n) (integerp i) (not (equal i 0)) (not (< i 0)))
         (< (m2 (+ n 1) (- i 1)) (m2 n i)))

         
(defunc f2 (n i)
 :input-contract (and (natp n)(integerp i))
 :output-contract (natp (f2 n i))
 (if (equal i 0)
    0
    (if (< i 0)
      (f2 n (+ i 1))
      (f2 (+ n 1)(- i 1)))))
      
(defunc m2 (n i)
 :input-contract (and (natp n)(integerp i))
 :output-contract (natp (m2 n i))
 (if (equal i 0)
     i
     (if (< i 0)
         (+ n (* i i))
         (- (+ n i) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
3. Assuming lon (list of naturals) is defined
For first recursive call:
(implies (and (lonp l)(natp n)(not (and (equal n 0)(endp l)))(> n 0))
         (< (m3 l (- n 1)) (m3 l n)))
For second recursive call:
(implies (and (lonp l)(natp n)(not (and (equal n 0)(endp l)))(equal n 0))
         (< (m3 (rest l) n) (m3 l n)))

(defunc f3 (l n)
 :input-contract (and (lonp l)(natp n))
 :output-contract (natp (f3 l n))
(if (and (equal n 0)(endp l))
    0
    (if (> n 0)
        (f3 l (- n 1))
        (f3 (rest l) n))))
         

(defunc m3 (l n)
 :input-contract (and (lonp l)(natp n))
 :output-contract (natp (m3 l n))
    (+ n (len l)))

Observe that the functions f1, f2, f3 are not unique - there are multiple 
suitable  candidates that satisfy our constraints.
|#


#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MORE ON TERMINATION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
4. A function that counts

Consider the following function definition:

(defunc o-count (i j c)
  :input-contract (and (natp i) (natp j) (natp c))
  :output-contract (natp (o-count i j c))
  (cond ((and (equal i 0) (equal j 0)) c)
        ((> j 0) (o-count i (- j 1) (+ c 1)))
        (t       (o-count (- i 1) 7 (+ c 1)))))

(a) Consider the call (o-count 2 3 0). Below are the first three argument
tuples that appear in recursive calls to o-count. Show the next three:

(2 3 0)  (2 2 1)  (2 1 2)  
(2 0 3) (1 7 4) (1 6 5)

What does (o-count 2 3 0) evaluate to? 
19

(b) Using the insights generated in (a), show that function o-count
terminates, by defining a measure function, and proving condition 4 as
outlined in hw07 (You can use equational reasoning to formalize your approach
but a basic set of arithmetic equalities will suffice).  What does the "o" in o-count
stand for (try (1 0 0) and (2 0 0) if you are still unsure)?  That may help you find a 
good measure function.  Your measure should only involve arithmetic.

Your proof will involve multiple scenarios since i may or may not change.

(defunc m (i j c)
 :input-contract (and (natp i) (natp j) (natp c))
 :output-contract (natp (o-count i j c))
 (if (> j 0)
     j
     i))
     
(implies (and (natp i)(natp j)(natp c)
         (not (equal i 0)) (> j 0))
                       (< (m i (- j 1) (+ c 1)) (m i j c)))

(implies (and (natp i)(natp j)(natp c) 
         (not (equal i 0)) (not (> j 0)))
                       (< (m (- i 1) j (+ c 1)) (m i j c)))
                       
=====================================================================
Case 1:                       
C1. (natp i)
C2. (natp j)
C3. (natp c)
C4. (> j 0)
C5. (not (equal i 0))

(m i (- j 1) (+ c 1))
= {def m, C1, C2, C3, C4}
(- j 1)
< {Arithmetic}
j
= {def m, C1, C2, C3}
(m i j c)

======================================================================
Case 2:
C1. (natp i)
C2. (natp j)
C3. (natp c)
C4. (not (> j 0))
C5. (not (equal i 0))

(m (- i 1) j (+ c 1))
= {def m, C1, C2, C3, C4}
(- i 1)
< {Arithmetic}
i
= {def m, C1, C2, C3}
(m i j c)
=======================================================================


|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 5. Fixing a non-terminating function
#|
(a) Mark is considering the following function:

    (defunc wicked (a b c)
      :input-contract (and (integerp a) (posp b) (integerp c))
      :output-contract (integerp (wicked a b c))
      (cond ((>= a b) a)
            ((>= b c) b)
            ((< c 0)  (wicked (+ a b) b c))
            (t        (wicked a b (+ a b)))))

He claims that this function will be admitted by ACL2s since its body is a
legal expression satisfying all body contracts, and the output contract is
trivially satisfied as well. But he forgot something! Show that the
function does not (always) terminate, by giving an input in the form of
concrete values a,b,c that satisfies the input contract but causes an
infinite execution.

(wicked 5 10 15)

(b) Mark admits there were several typos in his definition. His new
proposal is (read carefully!):
      

"Prove" that this function terminates by writing a measure function and 
showing that the value decreases for each condition (full equational reasoning
proofs are not necessary)

Hint: First run function wicked-awesome on a few well-chosen test cases 
(exercising all clauses of the cond) and see what happens. How long can 
chains of recursive calls to this function actually be?  Feel free 
to assume the absolute value function abs has already been defined. 
You do not need to formally prove termination but you must address all 
scenarios when a recursive call occurs.

Be sure that m would be admitted by ACL2s. Then prove that, on every
recursive call of wicked-awesome, the value of m decreases, under the conditions of
that recursive call.

(defunc wicked-awesome (a b c)
  :input-contract (and (integerp a) (posp b) (integerp c))
  :output-contract (integerp (wicked-awesome a b c))
  (cond ((>= a b) a)
        ((< c 0)  (wicked-awesome (+ a b) b c))
        (t        (wicked-awesome a b (- a b)))))

(defunc m-wickawesome (a b c)
  :input-contract (and (integerp a) (posp b) (integerp c))
  :output-contract (natp (m-wickawesome a b c))
  (cond ((>= a b) 0)
        ((< c 0)  (abs (- b a)))
        (t        (abs (- b (- a 1))))))

(test? (implies (and (integerp a) (posp b) (integerp c)
                     (not (>= a b))(< c 0))
                (< (m-wickawesome (+ a b) b c) (m-wickawesome a b c))))
                
(test? (implies (and (integerp a) (posp b) (integerp c)
                     (not (>= a b))(not (< c 0)))
                (< (m-wickawesome a b (- a b)) (m-wickawesome a b c))))

=======================================================================
Case 1:
C1. (integerp a)
C2. (posp b)
C3. (integerp c)
C4. (not (>= a b))
C5. (< c 0)

(m-wickawesome (+ a b) b c)
= {def m-wickawesome, C1, C2, C3, C4, C5}
(+ a b)
< {Arithmetic, def m-wickawesome, C1, C2, C3}
(m-wickawesome a b c)

=======================================================================
Case 2:
C1. (integerp a) 
C2. (posp b) 
C3. (integerp c)
C4. (not (>= a b))
C5. (not (< c 0)))

(m-wickawesome a b (- a b))
= {def m-wickawesome, C1, C2, C3, C4, C5}
(- a b)
< {Arithmetic, def m-wickawesome, C1, C2, C3}
(m-wickawesome a b c)

        
|#
#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
6. Prove termination for the following function:
 
(defunc ft2 (x y)
  :input-contract (and (listp x) (integerp y))
  :output-contract (natp (ft2 x y))
  (cond ((and (endp x) (equal y 0)) (+ 1 (len x)))
        ((and (endp x) (> y 0))     (+ 1 (ft2 x (- y 1))))
        ((endp x)                   (+ 1 (ft2 x (+ 1 y))))
        (t                          (+ 1 (ft2 (rest x) (- 0 y))))))

Hint: Note that you can start by writing candidate measures for each branch 
above that has a recursive call. However, you might be finally able to 
combine some/all of these measures to come up with one that works in all 
the 3 relevant cases above.

Define a measure function m:

(defunc m (x y)
 :input-contract (and (listp x) (integerp y))
 :output-contract (natp (m x y))
 (+ (len x) (abs y)))

        
(implies (and (listp x) (integerp y)(not (and (endp x) (equal y 0)))
                (and (endp x) (> y 0))) 
                (< (m-ft2 x (- y 1)) (m-ft2 x y)))
                
(implies (and (listp x) (integerp y)(not (and (endp x) (equal y 0)))
                (not (and (endp x) (> y 0)))(not (and (endp x) (> y 0)))
                (endp x))
                (< (m-ft2 x (+ 1 y)) (m-ft2 x y)))

(implies (and (listp x) (integerp y)(not (and (endp x) (equal y 0)))
                (not (and (endp x) (> y 0)))(not (and (endp x) (> y 0)))
                (not (endp x)))
                (< (m-ft2 (rest x) (- 0 y)) (m-ft2 x y)))

 
 
 
 

Then prove that the above defined function m is indeed a measure for ft2. 
....................
|#

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Question 7: The Return of PropEx
Let's prove that you are smarter than ACL2s.  Take your previous definition 
involving PropEx:

(defdata UnaryOp '~)
(defdata BinaryOp (enum '(^ v => == <>)))
(defdata prop-var (oneof 'a 'b 'c 'd 'e 'f 'p
                         'q 'r 's 'x 'y 'z)) 
(defdata PropEx 
  (oneof boolean 
         prop-var 
         (list UnaryOp PropEx) 
         (list PropEx BinaryOp PropEx)))

(defunc get-pxvars (px)
  :input-contract (PropExp px)
  :output-contract (Lovp (get-pxvars px))
  (cond ((booleanp px) nil)
        ((prop-varp px) (list px))
        ((UnaryOpp (first px)) (get-pxvars (second px)))
        (t (merge-nodups (get-pxvars (first px))
                         (get-pxvars (third px))))))

Prove that get-pxvars terminates by giving a measure function m and
proving that the value from m decreases each recursive call. Remember
that measure functions can use any admitted functions in ACL2s, including functions
in this file (use the simplest one that works).
**Let us make your lives easier by only having you prove m decreases
under the conditions of a single recursive case (choose) with that case's
input parameter changes.**

(defunc m-get-pxvars (px)
  :input-contract (PropExp px)
  :output-contract (natp (m-get-pxvars px))
  (cond ((booleanp px) 0)
        ((prop-varp px) 0)
        ((UnaryOpp (first px)) (max-depth px))
        (t (abs (+ (max-depth (first px))
                         (max-depth (third px)))))))

(test? (implies (and (PropExp px)(not (booleanp px))(not (prop-varp px))(UnaryOpp (first px)))
                (< (m-get-pxvars (second px)) (m-get-pxvars px))))
                
                
                
                
                
Tried to prove second branch but couldn't

(test? (implies (and (PropExp px)(not (booleanp px))(not (prop-varp px))(not (UnaryOpp (first px))))
                (< (+ (m-get-pxvars (first px))(m-get-pxvars (third px))) 
                   (m-get-pxvars px))))

|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;MORE MEASURE FUNCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
For each of the following terminating functions, write a measure function. You 
DO NOT need to prove that the function is a measure, just write the measure 
function in ACL2s syntax. These exercises are intended you to give additional 
practice coming up with measure functions. You are encouraged to do the proofs 
for additional practice, but you are NOT required to submit the proofs.

8.
(defunc do-nothing (x y z)
 :input-contract (and (listp x)(listp y)(integerp z))
 :output-contract (listp (do-nothing x y z))
 (cond (and (endp x)(equal z 0)  y)
       ((not (endp x)) (do-nothing (rest x) (cons (first x) y) z))
       ((< z 0) (do-nothing (cons z x) y (+ z 1)))
       (t       (do-nothing  x (cons z y) (- z 1)))

(defunc m (x y z)
 :input-contract (and (listp x) (listp y) (integerp z))
 :output-contract (natp (m x y z))
 (abs z))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
9.
(defunc do-something (x y)
  :input-contract (and (natp x) (listp y))
  :output-contract (booleanp (do-something x y))
  (cond ((equal x (len y)) t)
        ((> x (len y))(do-something (- x 1) y))
        (t (do-something (len y) '(x x x x)))))

(defunc m (x y)
 :input-contract(and (natp x) (listp y))
 :output-contract (natp (m x y))
 (+ x (len y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
10. NOT GRADED:  This is just a challenge question that I love.
(defunc widow-maker (x y)
  :input-contract (and (natp x) (natp y))
  :output-contract (booleanp(widow-maker x y))
  (cond ((equal x y) t)
        ((> x y)(widow-maker (- x 1) (+ y 1)))
        (t (widow-maker (+ y 1) x))))

................

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
11.
(defunc do-anything(x y)
  :input-contract (and (natp x) (natp y))
  :output-contract (booleanp(do-anything x y))
  (cond ((equal x y) t)
        ((> x y)(do-anything x (+ y 1)))
        (t (do-anything x (- y 1)))))
      
(defunc m (x y)
 :input-contract (and (natp x) (natp y))
 :output-contract (natp (m x y))
 (if (> x y)
 (- x y)
 (+ x y)))
 
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
12. Introduction to Induction
We will be looking at inductive proofs (in various forms) for the remainder of term.
Prove the following conjectures using induction.

If you want an example of an inductive proof, look at our proof for 
phi_inapp: (listp X) /\ (listp y) /\ (in a X) => (in a (app X Y)). 
We did this when looking at equational reasoning.  

We broke that proof into 3 parts
(after looking at the definition of "in") and proved 
phi_inapp1: (endp X) => phi_inapp
phi_inapp2: (consp X) /\ (equal (first X) a) => phi_inapp
phi_inapp3: (consp X) /\ (not (equal (first X) a)) /\ 
               ((listp (rest X)) /\ (listp Y) /\ (in a (rest X)) 
                     => (in a (app (rest X) Y))) 
            => phi_inapp
You might recall that I talked about a "fake induction" part 
of the proof for phi_inapp3

Notice that exportation means we just get a sequence of ands which imply 
(in a (app X Y)) for each of the conjectures.

These three conjectures are the induction scheme derived from in. 
For each induction scheme conjecture we add the conditions that 
lead to a particular function branch.  We also assume that the 
conjecture holds for the next recursive call.  Thus we substitute 
variables in the conjecture to what they will be at the next recursive call.

Note: for our inductive proofs we will also add a "bad data" case for completeness:
phi_inapp0: (not (listp X)) => phi_inapp.  We will frequently say "trivial" 
for these cases later on but let's see why this in in the phi-sumnl 
proof below.


1) Prove the following conjecture using the given induction schemes:
phi-sumnl: (implies (lonp l) (>= (sum-lon l) 0))

Where:
(defdata lon (listof nat))

(defunc sum-lon (l)
 :input-contract (lonp l)
 :output-contract (intp (sum-lon l))
 (if (endp l)
   0
   (+ (first l) (sum-lon (rest l)))))

and the induction scheme used (derived from listp) is:
1) (implies (and (not (consp l))(lonp l))
         phi-sumnl)
2) (implies (and (lonp l)(not (endp l))(phi-sumn1| ((l (rest l)))))
         (phi-sumnl))
or in other words
2) (implies (and (listp l)(not (endp l))
                 (implies (lonp (rest l)) (>= (sum-lon (rest l)) 0)))
            (implies (lonp l) (>= (sum-lon l) 0)))

Prove the conjectures so you can conclude (by induction) phi-sumnl is a theorem

=============================================
Case 1:
C1. (not (consp l))
C2. (lonp l)

0 = {C1,C2, Def Sum-lon}
(>= 0 0)
={arithmatic}
t

=============================================
Case 2:
C1. (lonp l)
C2. (not (endp l))
C3. (implies (lonp (rest l)) (>= (sum-lon (rest l)) 0))
--------------------------------------------------------
C4. (lonp (rest l)) ={C1, C2, def lonp}
C5. (>= (sum-lon (rest l)) 0) ={MP, C3, C4}

(sum-lon l)
={Def sum-lon, C1, C2}
(+ (first l) (sum-lon (rest l)))
={Def lonp, first-rest axiom, Decreasing len axiom, C1, C5, Def natp}
(>= (sum-lon l) 0)
t

==============================================


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


2) Prove the following conjecture
phi_poweven: (implies (and (rationalp x)(natp p))
                      (>= (pow x (* p 2)) 0))
Where
(defunc power (x p)
  :input-contract (and (rationalp x) (natp p))
  :output-contract (rationalp (power x p))
  (if (equal p 0)
    1
    (* x (power x (- p 1)))))

We will use the induction scheme for nind which gives us the following
proof obligations:

phi_poweven1: (implies (not (natp p)) phi_poweven)
thus solve (implies (and (not (natp p)) (rationalp x)(natp p))
                    (>= (pow x (* p2)) 0))
......this is the "trivial" condition mentioned above.

phi_poweven2: (implies (and (natp p)(equal p 0)) phi_poweven)
phi_poweven3: (implies (and (natp p)(> p 0)
                       (implies (and (rationalp x)(natp (- p 1))) (>= (power x (* (- p 1) 2)) 0))) 
              phi_poweven)

Prove the three sub-conjectures to prove that phi-poweven is a theorem.
You can use the following theorem without proving it:
T_esquare: (implies (rationalp r)(>= (* r r) 0))

==============================================
Case 1:
C1. (not (natp p)
C2. (natp p)
C3. nil = {C1, C2}

nil -> x = t

==============================================
Case 2:
C1. (natp p)
C2. (equal p 0)

(>= 1 0)
={C1, C2, Def power}
t

==============================================
Case 3:
C1. (natp p)
C2. (> p 0)
C3. (rationalp x)
C4. (natp (- p 1)))
C5. (>= (power x (* (- p 1) 2)) 0)))

(* x (power x (- p 1)))
={def power, C1, C2}
(* x x (power x (* (- p 1) 2))
={def power, C1, C2, C4}
(>= (* x x (power x (* (- p 1) 2))) 0)
= {T_esquare, C3, C5, C4}
t


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|#