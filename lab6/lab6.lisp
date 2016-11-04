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
CS 2800 Lab 6: Exam Review
--------------------------------
In this lab we will simply review materials covered on exam 1. If you don't 
understand a topic and there is no example below, ask the TA and they can probably
generate a representative question.

We've provide too many questions to be done during the lab time so that you won't
run out of sample problems to work on. You aren't expected to finish all of these 
questions.

Question 1:
For those of you that didn't do the bonus question in lab 5 last week, here it 
is again.
Prove:

(implies (listp x) 
     (and (implies (endp x)
                   (equal (len2 (rev2 x))
                          (len2 x)))
              (implies (and (not (endp x))
                            (equal (len2 (rev2 (rest x)))
                                   (len2 (rest x))))
                       (equal (len2 (rev2 x))
                              (len2 x)))))

Notice that we need to break down this conjecture into parts: where x is nil and 
when x is a cons (or not endp in to be more precise.

..........................

;;;;;;;;;;;;;;;;;
QUESTION 2:
;;;;;;;;;;;;;;;;;
 Consider the following definitions:
 
 (defunc no-dupesp (l)
  :input-contract (listp l)
  :output-contract (booleanp (no-dupesp l))
  (cond ((endp l)  t)
        ((in (first l) (rest l)) nil)
        (t             (no-dupesp (rest l)))))

(defunc num-unique-elements (l)
  :input-contract (listp l)
  :output-contract (natp (num-unique-elements l))
  (cond ((endp l)  0)
        ((in (first l)(rest l)) 
         (num-unique-elements (rest l)))
        (t                      
         (+ 1 (num-unique-elements (rest l))))))

;; Prove: (listp l)/\(no-dupesp l) => (num-unique-elements l) = (len l)

;; Break into 2 cases:
(implies (and (listp l)(endp l)(no-dupesp l))
         (equal (num-unique-elements l)(len l))) 

(implies (and (listp l)(not (endp l))(no-dupesp l)
              (implies (listp (rest l))
                       (equal (num-unique-elements (rest l))
                              (len (rest l)))))
         (equal (num-unique-elements l)(len l))) 

.............         
         
         
BONUS QUESTION: Length of rev
Prove
(implies (listp y)
         (equal (len (rev (cons x y)))
                (+ 1 (len (rev y)))))

Hint: output contract of rev. If you make use of that, make sure you quote
an appropriate theorem or axiom.

...

Recall that rev is defined as:
(defunc rev (x)
  :input-contract (listp x)
  :output-contract (and (listp (rev x)) (equal (len x) (len (rev x))))
  (if (endp x)
    nil
    (app (rev (rest x)) (list (first x)))))
    
and len is defined as:
(defunc len (x)
  :input-contract t
  :output-contract (natp (len x))
  (if (atom x)
    0
    (+ 1 (len (rest x)))))


|#

#|
;;;;;;;;;;;;;;;;;;
QUESTION 3
;;;;;;;;;;;;;;;;;;
For the following functions we only know the signature:

d: List -> All ???
m: Nat x List -> NatList replace all elements with that num
f: List -> Nat len
s: EvenList -> List adds odds?

the conjecture c is

(d (m x l)) = (f (s l))

Conjecture with hypotheses (contract checking and completion):
(implies (and (natp x)(listp l)(listp (m x l))(listp (s l)))
         (equal (d (m x l)) 
                (f (s l))))

                
Now define four functions d, m, f, s (as simple as possible) with the above
signatures. The actual outputs of the functions can be arbitrary, as long as
they satisfy the output contract and the conjecture you wrote above holds. 
For example, for m, you may choose to
simply return the constant nil, which is a natlist.

..............
;; d: List -> all
;; returns the first element of any list
(defunc d (l)
     :ic (listp l)
     :oc t
 (if (endp l)
   nil
   (first l)))
   
;; m: nat x list -> natlist
;; replaces all elements of a list with given natural
(defunc m (x l)
     :ic (and (natp x) (listp l))
     :oc (natlistp (m x l))
 (if (endp l)
   nil
   (cons nat (m x (rest l)))))
   
;; f: list -> nat 
(defunc len (l)
     :ic (listp l)
     :oc (natp l)
 (if (endp l)
    0
    (+ 1 (len (rest l)))))
    
;; s: evenlist -> list
;; adds the number one to the front of the even list
(defunc s (l)
   :ic (evenlistp l)
   :oc (listp l)
 (cons 1 l))

|#

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
QUESITON 4: Programming
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
|#

;; Write a set of data definitions to define the set of student exam marks.
;; Each exam has a student name and a list of 6 questions.  Each question 
;; should have a string name, number of points earned  and total points available.
;; For simplicity, we will call a list of exams a "loe".  Points per question
;; are 0 or more points but part marks are possible.

............


;; Now define the following functions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get-quest: nat x exam -> e-question
;; (get-quest i l) gets a particular exam question
;; from the exam.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
...........

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; q-mean: loe x nat -> grade
;; (q-mean l) takes a list of student exams and returns the average
;; grade for that question.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
............

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; s-grade: string x loe -> grade
;; (s-mean l) takes a list of student exams and the student's name
;; and returns the student's grade on the exam
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; BONUS QUESTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; power : Rational x Nat -> Rational
;;
;; (power x p) is x raised to the pth power. For example, x raised to the 3rd
;; power is x * x * x.

(check= (power 0 0) 1)
(check= (power 5/3 2) 25/9)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define
;; diff : Rationallist - {()} -> Rationallist
;;
;; (diff l) is the list of differences between successive elements of l,
;; where l is a list with at least one element. If l has only one or 0 elements,
;; then the list of differences is empty.

(check= (diff (list 1 2 3 4)) (list -1 -1 -1))
(check= (diff (list 2 8 3)) (list -6 5))
