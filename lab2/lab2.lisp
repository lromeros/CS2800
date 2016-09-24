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
;; Part 1: Evaluates to <?> 

; For each of these, try to predict what the left-hand-side of the
; equality will evaluate to and then replace the # with the correct
; value -- in the canonical form ACL2 prints when passed that
; expression in the read-eval-print loop.  For example:
;
;   (check= (/ 3 2) #)
;
; should become
;
;   (check= (/ 3 2) 3/2)
;
; which is accepted by ACL2 after moving the line past it.  (The
; arguments to CHECK= must be equal for ACL2 to accept the check.)
; What you fill in should be an atom, written differently if the left
; hand side is already an atom.
;
; This should be done in beginner mode. Notice that in beginner mode
; ACL2s prints out answers in a student-friendly way, e.g., evaluating 
; (list 1 2) at the REPL results in (list 1 2). In more advanced modes, 
; the result will be (1 2). So, like in Racket, there are various
; mode-specific features.

; first, rest, cons, list
(check= (first (cons 1 (cons 2 nil))) 1)
(check= (rest  (cons 1 (cons 'a nil))) '(a))            
(check= (rest  (list 1 2 3)) '(2 3))
(check= (equal (cons 1 (cons 2 nil)) (list 1 2)) t)
(check= (equal (cons 2 (cons 1 nil)) (list 1 2)) nil)
(check= (first (rest '(1 2 3))) 2) 

; predicates
(check= (natp (+ 1/2 5/2))       t)
(check= (rationalp (- 16 32))    t)
(check= (endp (cons t nil))      nil)
(check= (consp (list))           nil)
(check= (natp 16)                t)
(check= (rationalp 16)           t)
(check= (posp (- 1 -1))          t)

;; Part 2: Recursive Definitions

; You have to provide definitions for the function stubs below. You
; can use auxiliary definitions, if you need them. You have to use the
; design recipe and the design guidelines presented in class.
; Make sure that the check='s and test?'s below pass.
; Provide at least 4 check='s of your own if check='s are not provided. 

; odd-integerp: integer -> Boolean
; Usage: Returns true if x is an odd integer, nil otherwise.
; This should be a recursive definition.
(defunc odd-integerp (x)
  :input-contract (integerp x)
  :output-contract (booleanp (odd-integerp x))
  ;(not (integerp (/ x 2)))
  (cond ((equal x 0) nil)
        ((< x 0)(not (odd-integerp (+ x 1))))
        (t (not (odd-integerp (- x 1))))))
 

(check= (odd-integerp 1) t)
(check= (odd-integerp 0) nil)
(check= (odd-integerp -1) t)
(check= (odd-integerp 4802) nil)

(defdata loi (listof integer))

; all-oddp: loi -> Boolean
; Usage: Returns t if all elements in l are odd, nil otherwise.
(defunc all-oddp (l)
  :input-contract (loip l)
  :output-contract (booleanp (all-oddp l))
  (if (endp l)
    nil
    (if (odd-integerp (first l))
      (if (endp (rest l))
        t
        (all-oddp (rest l)))
      nil)))

(check= (all-oddp nil) nil)
(check= (all-oddp '(1)) t)
(check= (all-oddp '(1 2)) nil)
(check= (all-oddp (cons 1 '(1))) t)
(check= (all-oddp (cons 1 '(2))) nil)
(defconst *e* 0)

; =======================================================================+
; Define                                                                 |
; has-elementp: Any x List -> Boolean                                    |
;                                                                        |
; (has-elementp e l) returns true if and only if element e can be        |       
; found as a top level element in l (in other words you don't have       |
; to recursively search lists within l).                                 |
; -----------------------------------------------------------------------+
(defunc has-elementp (e l)
  :input-contract (listp l)
  :output-contract (booleanp (has-elementp e l))
  (if (endp l)
    nil
    (if (equal (first l) e)
      t
      (has-elementp e (rest l)))))

(check= (has-elementp 'a '(b c a)) t)
(check= (has-elementp 'a '(b c d)) nil)
(check= (has-elementp 'a '(b c (a b c))) nil)
(check= (has-elementp 0 '(0 A)) t)
(check= (has-elementp '() '()) nil)
(check= (has-elementp nil '(1 2 3)) nil)
; -----------------------------------------------------------------------
; replace-element: All x All x List -> List
; Usage: Replaces every element of l which is equal to old by new.

; (OLD T) (NEW NIL) (L (LIST (LIST 'X 'X) 0))
(defconst *o1* 0)
(defconst *l1* (list t t))
(defconst *n1* (list nil 0))

;  (OLD 0) (NEW 0) (L (LIST 0 T NIL))
(defconst *o3* 0)
(defconst *l3* (list 0 t nil))
(defconst *n3* 0)

; (OLD NIL) (NEW (LIST 'YX 'YX)) (L (LIST NIL NIL))
(defconst *l4* (list nil nil))
(defconst *n4* (list 'yx 'yx))

(defunc replace-element (old new l)
  :input-contract (listp l)
  :output-contract (listp (replace-element old new l))
  (if (has-elementp old l)
      (if (equal old new)
        l
        (if (equal (first l) old)
          (cons new (replace-element old new (rest l)))
          (cons (first l)(replace-element old new (rest l)))))
      (if (endp l)
        nil
        l)))

(check= (replace-element *o1* *n1* *l1*) *l1*)
(check= (replace-element *o3* *n3* *l3*) *l3*)
(check= (replace-element nil *n4* *l4*) (list *n4* *n4*))
(check= (replace-element 1 3 nil) nil)

; check that replace-element does not change len l
(test? (implies (listp l) 
                (equal (len (replace-element old new l))
                       (len l))))

; if old=new then replace-element is identity
(test? (implies (listp l) 
                (equal (replace-element x x l)
                       l)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Define
; all-identp: List -> Boolean
;
; (all-identp l) returns t if all elements in l are the same and nil otherwise.
; A helper function can be used but it is not strictly necessary.

(defunc all-identp (l)
  :input-contract (listp l)
  :output-contract (booleanp (all-identp l))
  (if (or (endp l)(endp (rest l))
          (equal (len l) 1))
    t
    (if (equal (first l)(first (rest l)))
      (all-identp (rest l))
      nil)))
  
(check= (all-identp '(1))   t)
(check= (all-identp '(1 a)) nil)
(check= (all-identp '()) t)
(check= (all-identp '(luna luna luna)) t)
(check= (all-identp '('('(nil nil) 'x nil))) t)
(check= (all-identp '(0 'x nil nil)) nil)
(check= (all-identp '(t nil)) nil)
;--------------------------------------------------------------------------

(defdata lor (listof rational))

; ordered-elementp: lor -> Boolean
; Usage: Returns t if l is ordered with respect to <, nil otherwise.
(defunc ordered-elementp (l)
  :input-contract (lorp l)
  :output-contract (booleanp (ordered-elementp l))
  (if (endp l)
    nil
    (if (equal (len l) 1)
      t
      (if (< (first l)(first (rest l)))
        (if (endp (rest (rest l)))
          t
          (ordered-elementp (rest l)))
        nil))))
      

(check= (ordered-elementp '(1 3/2 8/5)) t)
(check= (ordered-elementp '(1 3/2 15/10)) nil)
(check= (ordered-elementp '()) nil)
(test? (implies (and (listp l)(equal (len l) 1))
                t))

; contains-listp: list -> boolean
; returns t if this has at least one element that is non-empty list
(check= (rest '(1 '(3 3))) '('(3 3)))

(defunc contains-listp (l)
  :input-contract (listp l)
  :output-contract (booleanp (contains-listp l))
  (if (endp l)
    nil
    (if (listp (first l))
      t
      (if (endp (rest l))
        nil
        (contains-listp (rest l))))))

(check= (contains-listp '(1 2 3)) nil)
(check= (contains-listp '('(1))) t)
(check= (contains-listp nil) nil)

; has-elem-nestedp: Any List -> Boolean
; t if element exists within this list, even if within another list
(defunc has-elem-nestedp (e l)
  :input-contract (listp l)
  :output-contract (booleanp (has-elem-nestedp e l))
  (if (has-elementp e l)
    t
    (if (contains-listp l)
      (if (listp (first l))
        (has-elem-nestedp e (first l))
        (has-elem-nestedp e (rest l)))
      nil)))

(check= (has-elem-nestedp 3 '(3)) t)
(check= (has-elem-nestedp 3 '(1 '(3))) t)
(check= (has-elem-nestedp 3 nil) nil)
(check= (has-elem-nestedp nil '(3)) nil)
(check= (has-elem-nestedp nil nil) nil)
(check= (has-elem-nestedp 3 '('(2) 3 '(3 3) 2 3)) t)
(check= (has-elementp 3 '('(2) 3 '(3 3) 2 3)) t)

    
; delete: All x List  -> list
; Usage: Delete every occurrence of e in l
(defunc delete (e l)
  :input-contract (listp l)
  :output-contract (listp (delete e l))
  (if (endp l)
    nil
    (if (has-elem-nestedp e l)
      (if (equal (first l) e)
        (delete e (rest l))
        (if (listp (first l))
          (cons (delete e (first l))(delete e (rest l)))
          (cons (first l)(delete e (rest l)))))
      l)))


(check= (delete 3 (list (list 2) 3 (list 3 3) 2 3)) (list (list 2) nil 2)) 
(check= (delete 2 '(1 2 3 2 2)) '(1 3))
(check= (delete 2 nil) nil)
(check= (delete 2 '(1 3 4)) '(1 3 4))

; check that the length of delete is always <= length of l
(test? (implies (listp l)
                (<= (len (delete e l))
                    (len l))))#|ACL2s-ToDo-Line|#
