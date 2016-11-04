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

CS 2800 Homework 5 - Fall 2016

This homework is done in groups. The rules are:

 * ALL group members must submit the homework file (this file)

 * The file submitted must be THE SAME for all group members (we
   use this to confirm that alleged group members agree to be
   members of that group)

 * You must list the names of ALL group members below using the
   format below. If you fail to follow instructions, that costs
   us time and it will cost you points, so please read carefully.


Names of ALL group members: Prashan Parvani, Laura Romero-Suarez, Khyati Singh

Note: There will be a 10 pt penalty if your names do not follow 
this format.

For this homework you will NOT need to use ACL2s. However, you could
use the Eclipse/ACL2s text editor to write up your solution.

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Question 1: Applying a substitution.

Below you are given a set of ACL2 terms and substitutions. Recall
that a substitution is a list of 2-element lists, where the first
element of each list is a variable and the second an
expression. Also, variables can appear only once as a left
element of a pair in any substitution. For example, the
substitution ((y (cons a b)) (x m)) maps y to (cons a b) and x to
m. For each term/substitution pair below, show what you get when
you apply the substitution to the term (i.e., when you
instantiate the term using the given substitution) IF you can provide
such a substitution. If the substitution is invalid, indicate why.
Note: you do not need to calculate the returned value.


a. (rev2 (cons (app w y) z))
   ((w (list 3)) (y (app b c)) (z (rev2 b)))
   (rev2 (cons (app (list 3) (app b c)) (rev2 b)))


b. (cons c 'b)
   ((c (cons a (list b)) (b (cons c nil))))
   (cons (cons a (list b)) 'b)

c. (* (+ x (/ y (len z))) (+ (len z) y))
   ((x (+ a b)) (y (/ a b)) (z '(3 4)))
    (* (+ (+ a b) (/ (/ a b) (len '(3 4)))) (+ (len '(3 4)) (/ a b)))

d. (or (endp u) (listp (app u w)))
   ((u nil) (w (list (first x))) )
   (or (endp nil) (listp (app nil (list (first x)))))

e. (equal (+ (+ (len x) (len y)) (len z)) (len (cons 'z (app 'x y))))
   ((x '(5 6)) (y '(2 8)) (z '(17 3)))
   (equal (+ (+ (len '(5 6)) (len '(2 8))) (len '(17 3))) (len (cons 'z (app 'x '(2 8)))))

f. (app u w)
   ((w (app b a)) (w (list w)))
    Invalid -- you can't instantiate the same variable for 2 different values
               because the substitution takes place simultaneously
   
g. (app u w)
   ((w (app u w)) (u w))
   (app w (app u w))



Question 2: Finding a substitution, if it exists.
For each pair of ACL2 terms, give a substitution that instantiates the first to
the second. If no substitution exists write "None" and BRIEFLY explain why.

a. (app (rev2 a) (list b))
   (app (rev2 (cons (list (first x)) x)) (list (* z (len2 (rest x)))))
   ((a (cons (list (first x)) x)) (b (* z (len2 (rest x)))))

b. (add y z)
   (list 9 1)
   None, you cannot substitute in for a function. 


c. Here foo is a function that takes one argument
   (* (+ (/ z w) (- x (+ x 2))) (- u 4))
   (* (+ (/ (- (foo 5)(+ (foo 5) 2)) (foo 5)) (- a (+ a 2))) (- a 4))
   ((z (- (foo 5)(+ (foo 5) 2))) (w (foo 5)) (x a) (u a))


d. (app a (app 7 nil))
   (app x (app y nil))
   None, you can't substitue 7 for y, because 7 is a constant.


e. (app (list a) b)
   (app c (list d))
   None, you can't substitue (list a) for c, 
   because it is a function, and not a variable.


f. (in x y)
   (in x (rev2 z)) 
   ((x x)(y (rev2 z)))


g. (app a a)
   (app b c)
   None, a is one variable and cannot be subsituted for two different things. 

   
h. (cons y (app (list x)  y))
   (cons (- (expt 2 6) w) (app (list (- (expt 2 6) w)) (- (expt 2 6) q)))
   None, the values substituted for the two instances of y are different. 


|#



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; EQUATIONAL REASONING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

Questions 3 to 5 ask for equational proofs about ACL2
programs. In each question you will be given one or more function
definitions. The definitional axioms and contract theorems for
these functions can be used in the proof. You can use ACL2s to check
the conjectures you come up with, but you are not required to do
so. 

Here are some notes about equational proofs:

1. The context. Remember to use propositional logic to rewrite
the context so that it has as many hypotheses as possible.  See
the lecture notes for details. Label the facts in your
context with C1, C2, ... as in the lecture notes.

2. The derived context. Draw a line after the context and add
anything interesting that can be derived from the context.  Use
the same labeling scheme as was used in the context. Each derived
fact needs a justification. Again, look at the lecture notes for
more information.

3. Use the proof format shown in class and in the lecture notes,
which requires that you justify each step.

4. When using an axiom, theorem or lemma, show the name of the
axiom, theorem or lemma, and then show the instantiation you are
using.

5. When using the definitional axiom of a function, the
justification should say "Def function-name".  When using the
contract axiom of a function, the justification should say
"Contract function-name"......replacing function-name with the
actual function name of course.

6. Arithmetic facts such as commutativity of addition can be
used. The name for such facts is "arithmetic".

7. You can refer to the axioms for cons, consp, first and rest as
the "cons axioms". The axioms for if are named "if axioms" Any
propositional reasoning used can be justified by "propositional
reasoning", except that we will often use "MP" for modus
ponens. 

8. For this homework, you can only use theorems we explicitly
tell you you can use. You can, of course, use the definitional 
axiom and contract theorem for any function used or
defined in this homework. Here are the definitions used for the 
remainder of the questions.

(defunc len2 (x)
  :input-contract (listp len2x)
  :output-contract (natp (len2 x))
  (if (endp x)
    0
    (+ 1 (len2 (rest x)))))

(defunc duplicate (l)
  :input-contract (listp l)
  :output-contract (listp (duplicate l))
  (if (endp l)
    nil
    (cons (first l) (cons (first l) (duplicate (rest l))))))

(defdata natlist (listof nat))


(defunc in2 (a l)
  :input-contract (listp l)
  :output-contract (booleanp (in2 a l))
  (if (endp l)
    nil
    (or (equal a (first l)) (in2 a (rest l)))))

(defunc subsetp (l1 l2)
  :input-contract (and (listp l1) (listp l2))
  :output-contract (booleanp (subsetp l1 l2))
  (if (endp l1)
    t
    (and (in2 (first l1) l2) (subsetp (rest l1) l2))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


For each of the conjectures in questions 3-5:

- perform conjecture contract checking, and add hypotheses if necessary

- run some tests to make an educated guess as to whether the conjecture is
  true or false. In the latter case, give a counterexample to the
  conjecture, and show that it evaluates to false. Else, give a proof 
  using equational reasoning, following instructions 1 to 8 above.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
3.
(defunc big-foo (m n)
  :input-contract (and (natp m) (natp n))
  :output-contract (natp (big-foo m n))
  (cond ((equal m 0) (+ n 1))
        ((equal n 0) (big-foo (- m 1) 1))
        (t (big-foo (- m 1) (big-foo m (- n 1))))))

3a. Prove the following using equational reasoning:

(implies (natp n)
         (equal (big-foo 0 n) (+ 1 n)))
         
C1. (natp n)
---------------
C2. (>= n 0) {C1}

---------------------------------------------------------------------------
LHS:

(big-foo 0 n)
={Def big-foo, if axiom, C1, C2}
(+ n 1)

LHS === RHS
QED


3b. Prove the following using equational reasoning:

(implies (and (natp n)
              (equal n 0))
         (equal (big-foo 1 n) (+ 2 n)))

C1. (natp n)
C2. (equal n 0)

LHS:
(big-foo 1 n)
= {Def big-foo, C2, if axiom}
(big-foo (- 1 1) 1)
= {Subtraction axiom}
(big-foo 0 1)
= {Def big-foo, if axiom}
(+1 1))
= {Addition axiom}
2

======================================================
RHS:
------------------------------------------------------
(+ 2 n)
= {C2}
(+ 2 0)
= {Addition axiom}
2

LHS === RHS
QED


3c. Prove the following using equational reasoning:

(implies (and (natp n)
              (not (equal n 0))
              (implies (natp (- n 1))
                       (equal (big-foo 1 (- n 1)) (+ 2 (- n 1)))))
         (equal (big-foo 1 n) (+ 2 n)))

C1. (natp n)
C2. (n =! 0)
C3. (equal (big-foo 1 (- n 1)) (+ 2 (- n 1)))
C4. (natp (- n 1))
-------------------------------------------------
C5. (equal (+ 2 (- n 1)) (+ n 1)) = {C3, Addition axiom}
T2. (equal (big-foo 0 n) (+ 1 n)) = {Thereom justified in part 3a}


LHS
------------------
(big-foo 1 n) 
= {C2, C1, Def big-foo, if axiom}
(big-foo (- 1 1) (big-foo 1 (- n 1)))
= {Subtraction axiom}
(big-foo 0 (big-foo 1 (- n 1)))
= {Def big-foo, if axiom, T2, C1, C2, C4}
(+ 1 (big-foo 1 (- n 1)))
= {C3}
(+ 1 (+2 (- n 1)))
={C5}
(+1 (+ n 1))
= {Addition axiom}
(+ 2 n)

LHS === RHS 
QED

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
4.

(implies (listp l)
         (and (implies (endp l)
                       (subsetp l l))
              (implies (and (consp l)
                            (subsetp (rest l) (rest l)))
                       (subsetp l l))))

You can assume that the following is a theorem:

T1:  (implies (and (listp l1)
                     (listp l2)
                     (subsetp l1 l2))
                (subsetp l1 (cons a l2)))
                

LHS [Proof for (implies (endp l) (subsetp l l))]
-------------------------------------------------------

C1. (listp l)
C2. (endp l)
------------------------------
t 
= {C1, C2, Def subsetp, if axiom}

========================================================
RHS 
[Proof for (implies (and (consp l)
                         (subsetp (rest l) (rest l)))
                         (subsetp l l))))]
--------------------------------------------------------
                       
C1. (consp l)
C2. (listp l)
C3. (subsetp (rest l) (rest l))
---------------------------------
C4. (not (endp l)) = {C1}
C5. (equal (cons (first l) (rest l)) l) ={Cons axiom}


---------------------------------
(subsetp l l)
={Def subsetp, C1, C2, if axiom}
(and (in2 (first l) l) (subsetp (rest l) l))
={Def in2, if axiom, C1, C2}
(and (or (equal (first l) (first l)) (in2 (first l) (rest l)))) (subsetp (rest l) l))
={boolean axiom}
(and t (subsetp (rest l) l))
={C5, C4}
(and t (subsetp (rest l) (cons (first l) (rest l))))
={T1, C3}
(and t t)
={boolean axiom}
t

----------------------------------------------
Proof for the whole function: 

(implies (listp l) t)
={t implies t = t}

LHS === RHS
QED


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
5.

(implies (listp x)
         (and (implies (endp x)
                       (equal (len2 (duplicate x))
                              (* 2 (len2 x))))
                              
              (implies (and (not (endp x))
                            (equal (len2 (duplicate (rest x)))
                                   (* 2 (len2 (rest x)))))
                                   
                       (equal (len2 (duplicate x))
                              (* 2 (len2 x)))))))
LHS
-------------------------------------------------------
C1 -> (listp x)
C2 -> (endp x)

LHS-L
(len2 (duplicate x))
 = {C1, C2, def. of duplicate, if-axiom}

(len2 (nil))
 = {def, of len2, if-axiom}
0
 
LHS-R
(* 2 (len2 x))
 = {C1, C2, definition of len2, if-axiom}

(* 2 0)
 = {arithmetic}
0
========================================================
RHS
--------------------------------------------------------
C1 -> (listp x)
C2 -> (and (not (endp x)) 
           (equal (len2 (duplicate (rest x)))
             (* 2 (len2 (rest x)))))
------------------------------------------
C3 -> (consp x) = {C1, C2, cons axiom}
C4 -> (listp (rest x)) = {C1, C2, C3, definition of list, definition of cons}

RHS-L
(len2 (duplicate x))
 = {C4, substitute (x (rest x))}
(len2 (duplicate (rest x)))
 = {C2, C3}
(* 2 (len2 (rest x))) 

RHS-R
(* 2 (len2 x)) 
 = {substitute (x (rest x)), C4}
(* 2 (len2 (rest x))) 


RHS-L === RHS-R === T
LHS-L === LHS-R === T
LHS === RHS

QED

|#