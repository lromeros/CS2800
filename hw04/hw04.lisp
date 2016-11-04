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

CS 2800 Homework 4 - Fall 2016

The last problem in this homework requires you to see if two expressions
are equivalent.  This happens to be an equivalent problem to SAT or satisfiability.
Thus, all you need to claim the Clay Institute $1M Millennium
prize for solving the P vs NP problem is to either come up with an
efficient algorithm or show that no such algorithm exists! Who guessed
this course could lead to such easy money.

This homework is done in groups. The rules are:

 * ALL group members must submit the homework file (this file)

 * The file submitted must be THE SAME for all group members (we
   use this to confirm that alleged group members agree to be
   members of that group)

 * You must list the names of ALL group members below using the
   format below. If you fail to follow instructions, that costs
   us time and it will cost you points, so please read carefully.


Names of ALL group members: Laura Romero, Khyati Singh

Note: There will be a 10 pt penalty if your names do not follow 
this format.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For this homework you will need to use ACL2s.

Technical instructions:

- open this file in ACL2s as hw04.lisp

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

- when done, save your file and submit it as hw04.lisp

- avoid submitting the session file (which shows your interaction with the
  theorem prover). This is not part of your solution. Only submit the lisp
  file!

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
number of inputs.

Use good judgment. For unreasonably few test cases we will deduct points.
Remember,  your TAs can test your code any way they want. How confident
do you feel that they won't have a test that fails?

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

UPDATE: You should also use test? for your tests.  It takes the form
(test? (implies hyp concl)) 
such as:
(test? (implies (and (listp l)(natp n)) (<= (len (sublist-start n)) n))) 

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Propositional Logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

We use the following ascii character combinations to represent the Boolean
connectives:

  NOT     ~

  AND     /\
  OR      \/

  IMPLIES =>

  EQUIV   =
  XOR     <>

The binding powers of these functions are listed from highest to lowest
in the above table. Within one group (no blank line), the binding powers
are equal. This is the same as in class.

|#

#|

Construct the truth table for the following Boolean formulas. Use
alphabetical order for the variables in the formula, and create columns for
all variables occurring in the formula AND for all intermediate
subexpressions. (with one exception: you can omit basic negations such as ~p or ~r).
For example, if your formula is

(p => q) \/ r

your table should have 5 columns: for p, q, r, p => q, and (p => q) \/ r .

Then decide whether the formula is satisfiable, unsatisfiable, valid, or
falsifiable (more than one of these predicates will hold!). 


1. p => (~p /\ q) \/ q


Satisfiable, and falsifiable.
.=========================================================================.
|  p  |  q  |  ~p /\ q  |   (~p /\ q) \/ q    |    p => (~p /\ q) \/ q    |  
+-------------------------------------------------------------------------+
|  T  |  T  |     F     |          T          |            T              |        
|  T  |  F  |     F     |          F          |            F              |
|  F  |  T  |     T     |          T          |            T              |     
|  F  |  F  |     F     |          F          |            T              |  
+=========================================================================+



2. (p => q) /\ (~r = ~q) <> ~p => r  

Hint: your table should have 8 or 11 columns (including those for p,q,r)
depending on whether you have (optional) columns for ~ r ~q and ~p.
 

Satisfiable, and falsifiable.
.=======================================================================================================================.
|  p  |  q  |  r  |  (p => q)  |   ~r = ~q   |  (p => q) /\ (~r = ~q)  |  ~p => r  |  (p => q) /\ (~r = ~q) <> ~p => r  |
+-----------------------------------------------------------------------------------------------------------------------+
|  T  |  T  |  T  |      T     |      T      |            T            |     T     |                F                   |
|  T  |  T  |  F  |      T     |      F      |            F            |     T     |                T                   |
|  T  |  F  |  T  |      F     |      F      |            F            |     T     |                T                   |
|  T  |  F  |  F  |      F     |      T      |            F            |     T     |                T                   |
|  F  |  T  |  T  |      T     |      T      |            T            |     T     |                F                   |
|  F  |  T  |  F  |      T     |      F      |            F            |     F     |                F                   |
|  F  |  F  |  T  |      T     |      F      |            F            |     T     |                T                   |
|  F  |  F  |  F  |      T     |      T      |            T            |     F     |                T                   |
+=======================================================================================================================+
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
3. Simplify the following expressions using propositional logic rules (give 
either the rule name or the formula. Transformations should take the form:
   expression 1
   = {Justification}
   expression 2
   = {Justification}
   expression 3
   ......

(a) p <> p /\ (q \/ p)
   = {commutative}
   p <> p /\ (p \/ q)
   = {absorption}
   p <> p
   = {p <> p ≡ false}
   
   false
   ;; verified using truth table

(b) (p /\ r => ((q \/ ~p) => (~r => r)))
   = {p => ~p = false}
   (p /\ r => ((q \/ ~p) => false))
   = {p => false = ~p}   
    (p /\ r => (~(q \/ ~p)))
   = {DeMorgan's}
    (p /\ r => (~q /\ p))
   = {Commutative}
    (p /\ r => (p /\ ~q))
   = {p => q == ~p \/ q}
    (~(p /\ r) \/ (p /\ ~q))
   = {DeMorgan's}
   (~p \/ ~r) \/ (p /\ ~q)
   ;; verified using truth table

(c) (p \/ q) /\ ((~p \/ q) /\ ~q))
   = {Commutative}
   (p \/ q) /\ (~q /\ (~p \/ q)))
   = {Distributive}
    (p \/ q) /\ ((~q /\ ~p) \/ (~q /\ q))
   = {p /\ false = false}
     (p \/ q) /\ ((~q /\ ~p) \/ false)
   = {Identity}
     (p \/ q) /\ (~q /\ ~p)
   = {Commutative}
     (p \/ q) /\ (~p /\ ~q)
   = {DeMorgan's}
     (p \/ q) /\ ~(p \/ q)
   = {p /\ ~p = false}
     false
  ;; verified using truth table
  

(d) (p /\ ~q /\ r) \/ (p /\ ~q /\ ~ r) \/ (p /\ q /\ r) \/ (p /\ q /\ ~ r)
   = {Distributive (factoring)}
   (p /\ ~q) /\ r \/ ~r \/ (p /\ q) /\ r \/ ~r
   = {p \/ ~p = t}
   (p /\ ~q) /\ t \/ (p /\ q) /\ t
   = {Identity}
   (p /\ ~q) \/ (p /\ q)
   = {Distributive (factoring)}
   p /\ (~q \/ q)
   = {p \/ ~p ≡ t}
   p /\ t
   ={Identity}
   p
   ;; verified using truth table

(e) p => (~p <> q)
   = {p => q = ~p \/ q}
   ~p \/ (~p <> q) 
   ;; verified using truth table
   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

4. A QUICK CONTEMPLATIVE: Notice that in functional languages, two functions can be considered equivalent iff
for the same input, both functions return the same output.  In other words, there are exactly
two binary functions that take no input: one that returns t and one that returns nil.
For the following questions, thinking about truth tables may help.
a) How many binary Boolean functions f(x) are there where Boolean->Boolean? 
2^(2^n) 2^(2^1)= 2^2 = 4

b) How many functions f(x, y) (Boolean x Boolean -> Boolean) are there?
2^(2^n) 2^(2^2)= 2^4 = 16

c) For any binary function with n binary inputs (Boolean x Boolean x.....Boolean -> Boolean),
how many unique functions exist?  Think about the number of rows in the truth table.  The
out column is a string of t/nils.  How many different output strings are possible?

2^n possibly inputs, 2^(2^n) unique functions.
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Characterization of formulas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

For each of the following formulas, determine if they are valid,
satisfiable, unsatisfiable, or falsifiable. These labels can
overlap (e.g. formulas can be both satisfiable and valid), so
keep that in mind and indicate all characterizations that
apply. In fact, exactly two characterizations always
apply. (Think about why that is the case.) Provide proofs of your
characterizations, using a truth table or simplification
argument (for valid or unsatisfiable formulas) or by exhibiting
assignments that show satisfiability or falsifiability.

(A) q =  (p => (q => q))
   = {p=>p = true}
   q = (p => true)
   = {p => true = true}
   q = true
   
   falsifiable, q = false != true
   satisfiable, q = true = true
   ;; verified using truth table

(B) (p => q) = (~q /\ p)
   = {p => q = ~p \/ q}
   (~p \/ q) = (~q /\ p)
   = {Commutative}
   (~p \/ q) = (p /\ ~q)
   = {DeMorgan's}
    ~(p /\ ~q) = (p /\ ~q)
   = {p = ~p = false}
    false
   
   falsifiable, unsatisfiable 
   ;; verified with truth table

(C) (((false \/ ~ p) /\ p) => p)
   = {p \/ false = p}
   ((~p /\ p) => p)
   = {~p /\ p = false}
   (false => p)
   = {p => q = ~p \/ q}
    true \/ ~p
   = {true \/ p = true}
    true
   satisfiable, valid
   ;; verified with truth table

(D) [(~(p /\ q) \/ r) /\ (~p \/ ~q \/ ~r)] <> (p /\ q)
   = {DeMorgan's}
   [(~p \/ ~q) \/ r /\ (~p \/ ~q \/ ~r)] <> (p /\ q)
   
   = {Associative}
   [(~p \/ ~q \/ r) /\ (~p \/ ~q \/ ~r)] <> (p /\ q)
   
   = {Distributive (factoring)}
   [(~p \/ ~q) \/ (r /\ ~r)] <> (p /\ q)
   
   = {p /\ ~p = false}
   [(~p \/ ~q) \/ false] <> (p /\ q)
   
   = {p \/ false = p}
   (~p \/ ~q) <> (p /\ q)
   
   = {p <> q = [(p /\ ~q) \/ (~p /\ q)]
   [(~p \/ ~q) /\ ~(p /\ q)] \/ [~(~p \/ ~q) /\ (p /\ q)]

   = {DeMorgan's}
   [~(p /\ q) /\ ~(p /\ q)] \/ [(p /\ q) /\ (p /\ q)]
   
   = {p /\ p = p}
   ~(p /\ q) \/ (p /\ q)
   
   = {~p \/ p = true}
   true
   satisfiable, valid
   ;; verified with true table

(E) ~ (p => ~ q /\ q)
   = {~p /\ p = false}
   ~ (p => false)
   = {p => false = ~p}
   ~ (~p)
   = {~~p = p}
    p
  
   satisfiable, falsifiable
   ;; verified using truth table

|#



;; Leave this code alone:  It changes when ACL2s gives up on proving termination.
(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)
(set-defunc-timeout 80)
(acl2s-defaults :set cgen-timeout 2)

#|
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
Question 5: Two propositional expressions are equivalent if they have the
same truth tables.  Thus if  you evaluate all variable combinations
in both expressions and they evaluate to the same thing each time,
the expressions are the same.

Define the functions below so that two arbitrary propositional expressions
are evaluated for all possible variable values. If the two expressions do not
have the same result, then stop.  Otherwise test the next set of variable
assignments.

For example Expression X: (A ==> B ==> C) and Expression Y: (A /\ D) will be 
evaluated for variables ABCD = TTTT, FTTT, FFTT, FTFT, TFTT, ....
You may assume that variable names are consistent across formulas thus 
you are NOT looking to see if A in formula 1 maps to variable B in formula 2.

NOTE: you will have to do double recursion (like you did in Fundies).  If you don't
remember it, review your old notes.  It's also a very good idea to work through
a number of examples to make sure you understand how your code should work BEFORE
you begin coding.

Example: For Formula 1: (A=> B) and Formula 2: (~A \/ B), you need to evaluate 4
different variable assignments (4 rows in the truth tables).  
AB: FF FT TF TT.  Formula 1 and formula 2 both return T T F T and thus your 
function returns t.  (A=>B) and (~A <> B) returns T T/nil nil T and thus your
function should return nil.  How can you test all variable t/nil combinations?
How can you keep A as true and test t/nil values for the other variables?

For this exercise, some pre-generated code and definitions are provided.  
This code should *not* be modified.  You will use these functions in the 
functions you write.

|#
;; NOTE: We are keeping the code predominately in program mode.  If you can
;; get your code to work in logic mode with full proofs, I'll give a bonus.


; UnaryOp:   '~ means "not"

(defdata UnaryOp '~)

; BinaryOp: '^ means "and", 'v means "or", '=> means "implies",
; and '== means "iff". 

(defdata BinaryOp (enum '(^ v => == <>)))

;; The list of possible variable names.  Feel free to add to this list
;; but this avoids people using '<> or '^ as a variable.
(defdata prop-var (oneof 'a 'b 'c 'd 'e 'f 
                         'p 'q 'r 's 'x 
                         'y 'z))

; PropEx: A Propositional Expression (PropEx) can be a boolean (t
; or nil), a symbol denoting a variable (e.g. 'p or 'q), or a
; list denoting a unary or binary operation. 

(defdata PropEx 
  (oneof boolean 
         prop-var 
         (list UnaryOp PropEx) 
         (list PropEx BinaryOp PropEx)))

; IGNORE THESE THEOREMS. USED TO HELP ACL2S REASON
(defthm propex-expand1
  (implies (and (propexp x)
                (not (prop-varp x))
                (not (booleanp x)))
           (equal (second x)
                  (acl2::second x))))

(defthm propex-expand2
  (implies (and (propexp x)
                (not (prop-varp x))
                (not (booleanp x))
                (not (equal (first (acl2::double-rewrite x)) '~)))
           (equal (third (acl2::double-rewrite x))
                  (acl2::third (acl2::double-rewrite x)))))

(defthm propex-expand3
  (implies (and (propexp px)
                (consp px)
                (not (unaryopp (first px))))
           (and (equal (third px)
                       (acl2::third px))
                (equal (second px)
                       (acl2::second px))
                (equal (first px)
                       (acl2::first px)))))

(defthm propex-expand2a
  (implies (and (propexp x)
                (not (booleanp x))
                (not (prop-varp x))
                (not (unaryopp (first (acl2::double-rewrite x)))))
           (equal (third (acl2::double-rewrite x))
                  (acl2::third (acl2::double-rewrite x)))))

(defthm propex-lemma2
  (implies (and (propexp x)
                (not (booleanp x))
                (not (prop-varp x))
                (not (equal (first (acl2::double-rewrite x)) '~)))
           (and (propexp (first x))
                (propexp (acl2::first x))
                (propexp (third x))
                (propexp (acl2::third x)))))

(defthm propex-lemma1
  (implies (and (propexp x)
                (not (booleanp x))
                (not (prop-varp x))
                (equal (first (acl2::double-rewrite x)) '~))
           (and (propexp (second x))
                (propexp (acl2::second x)))))


(defthm first-rest-listp
  (implies (and l (listp l))
           (and (equal (first l)
                       (acl2::first l))
                (equal (rest l)
                       (acl2::rest l)))))
; END IGNORE (These are SLOOOOOOW.  Please be patient).


; An assignment is a mapping from symbols to booleans
(defdata Assignment (list prop-var boolean))

;; A list of assignments
(defdata Loa (listof Assignment))


; A list of vars
(defdata Lov (listof prop-var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; add: prop-var x LOV -> LOV
;; (add v X) take a variable v and adds it to the list of variables X
;; provided v is not already in X.
(defunc add (v X)
  :input-contract (and (prop-varp v) (Lovp X))
  :output-contract (Lovp (add v X))
  (if (in v X)
    X
    (cons v X)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; merge-nodups: Lov x Lov -> Lov
;; merge-nodups l1 l2) is a helper function allowing us to take two 
;; lists of variables l1 and l2 and merge them so we don't get duplicates
(defunc merge-nodups (l1 l2)
  :input-contract (and (lovp l1)(lovp l2))
  :output-contract (lovp (merge-nodups l1 l2))
  (if (endp l1)
    (if (endp l2)
      nil
      l2)
    (if (endp l2)
      l1
      (merge-nodups (rest l1) (add (first l1) l2)))))

(check= (merge-nodups '(a a c) '(c d e)) '(a c d e))
(check= (merge-nodups '(a b c) '(c c d e)) '(b a c c d e))
(check= (merge-nodups '(a b c) '(a b c)) '(a b c))
(check= (merge-nodups '(a b c) '()) '(a b c))
(check= (merge-nodups '() '(c d e)) '(c d e))
(check= (merge-nodups '() '()) '())

(test? (implies (Lovp l) (equal (merge-nodups l l) l)))
(check= (merge-nodups '(a b c) '(p q b r)) '(c a p q b r))


;; Because tracking down the performance problems is ruining
;; the homework, I'll make it easier.  HOWEVER, this means
;; that you should test more thoroughly.  Also, be very careful
;; not to create infinite loops.  ACL2s won't catch these any more.
 :program

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TO ADD
;; get-pxvars: PropEx -> Lov
;; (get-pxvars px) returns a list of variables appearing in px.
;; The returned list should have no duplicate variables in it.
;; Double recursion will be necessary.
;; Hint: you can use the function add above.
;; See the check='s and function update below for a potential 
;; example to work through.
(defunc get-pxvars (px)
  :input-contract (propexp px)
  :output-contract (lovp (get-pxvars px))
  (cond
   ((booleanp px) nil)
   ((prop-varp px) (list px))
   ((listp px) (if (equal (len px) 3)
                 (merge-nodups (get-pxvars (first px))
                               (get-pxvars (third px)))
                 (get-pxvars (second px))))))
; px is a boolean
(check= (get-pxvars t) nil)
(test? (implies (booleanp px)
                (endp (get-pxvars px))))

; px is a variable
(check= (get-pxvars 'a) '(a))
(test? (implies (prop-varp px)
                (and (equal 1 (len (get-pxvars px)))
                     (equal px (first (get-pxvars px))))))

; px is unary boolean exp
;   with boolean
(check= (get-pxvars (list '~ t)) nil)
(test? (implies (and (propexp px)
                     (and (listp px)(equal (len px) 2))
                     (booleanp (second px)))
                (endp (get-pxvars px))))
                
;   with variable
(check= (get-pxvars (list '~ 'a)) '(a))
(test? (implies (and (propexp px)
                     (and (listp px)(equal (len px) 2))
                     (prop-varp (second px)))
                (equal (list (second px))(get-pxvars px))))
;   with unary boolean exp
(check= (get-pxvars (list '~ (list '~ 'a))) '(a))
(test? (implies (and (propexp px)
                     (and (listp px)(equal (len px) 2))
                     (and (listp (second px))(equal (len (second px)) 2))
                     (not (booleanp (second (second px)))))
                (equal (list (second (second px)))(get-pxvars px))))

;   with binary boolean exp
(check= (get-pxvars (list '~ (list 'a '^ 'b))) '(a b))

; px is a binary boolean exp
;       with boolean x boolean
(check= (get-pxvars (list t '^ nil)) '())
;       with boolean x variable
(check= (get-pxvars (list t '^ 'a)) '(a))
;       with boolean x unary
(check= (get-pxvars (list t '^ (list '~ t))) '())
;       with boolean x binary
(check= (get-pxvars (list t '^ (list 'a '^ 'b))) '(a b))

;       with variable x boolean
(check= (get-pxvars (list 'a '^ t)) '(a))
;       with variable x variable
(check= (get-pxvars (list 'a '^ 'b)) '(a b))
(check= (get-pxvars (list 'a '^ 'a)) '(a))
;       with variable x unary 
(check= (get-pxvars (list 'a '^ (list '~ t))) '(a))
;       with variable x binary
(check= (get-pxvars (list 'a '^ (list 'a '^ 'b))) '(a b))
(check= (get-pxvars (list 'a '^ (list 'b '^ 'c))) '(a b c))

;       with unary x boolean
(check= (get-pxvars (list (list '~ t) '^ t)) '())
;       with unary x variable
(check= (get-pxvars (list (list '~ t) '^ 'a)) '(a))
(check= (get-pxvars (list (list '~ 'a) '^ 'b)) '(a b))
(check= (get-pxvars (list (list '~ 'a) '^ 'a)) '(a))
;       with unary x unary
(check= (get-pxvars (list (list '~ t) '^ (list '~ t))) '())
(check= (get-pxvars (list (list '~ 'a) '^ (list '~ 'a))) '(a))
(check= (get-pxvars (list (list '~ 'a) '^ (list '~ 'b))) '(a b))
;       with unary x binary
(check= (get-pxvars (list (list '~ t) '^ (list nil '^ t))) '())
(check= (get-pxvars (list (list '~ t) '^ (list 'a '^ 'b))) '(a b))
(check= (get-pxvars (list (list '~ 'a) '^ (list 'b '^ 'c))) '(a b c))
(check= (get-pxvars (list (list '~ t) '^ (list nil '^ 'a))) '(a))

;       with binary x boolean
(check= (get-pxvars (list (list nil '^ t) '^ t)) '())
(check= (get-pxvars (list (list nil '^ 'a) '^ t)) '(a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ t)) '(a b))
(check= (get-pxvars (list (list 'a '^ 'a) '^ t)) '(a))
;       with binary x variable
(check= (get-pxvars (list (list nil '^ 'a) '^ 'a)) '(a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ 'a)) '(b a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ 'c)) '(b a c))
(check= (get-pxvars (list (list 'a '^ 'a) '^ 'b)) '(a b))
;       with binary x unary
(check= (get-pxvars (list (list nil '^ t) '^ (list '~ t))) '())
(check= (get-pxvars (list (list nil '^ 'a) '^ (list '~ t))) '(a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ (list '~ 'c))) '(b a c))
(check= (get-pxvars (list (list 'a '^ 'b) '^ (list '~ 'a))) '(b a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ (list '~ t))) '(a b))
(check= (get-pxvars (list (list 'a '^ 'a) '^ (list '~ t))) '(a))
;       with binary x binary
(check= (get-pxvars (list (list nil '^ 'a) '^ (list t '^ 'a))) '(a))
(check= (get-pxvars (list (list nil '^ 'a) '^ (list t '^ 'b))) '(a b))
(check= (get-pxvars (list (list nil '^ 'a) '^ (list 'b '^ 'c))) '(a b c))
(check= (get-pxvars (list (list 'a '^ 'b) '^  (list 'a '^ 'b))) '(a b))
(check= (get-pxvars (list (list 'a '^ 'b) '^  (list 'b '^ 'c))) '(a b c))
(check= (get-pxvars (list (list 'a '^ 'b) '^  (list 'c '^ 'd))) '(b a c d))
(check= (get-pxvars (list (list 'a '^ 'b) '^ (list (list '~ 'a) 'v t))) '(b a))
(check= (get-pxvars (list (list 'a '^ 'b) '^ (list (list '~ 'c) 'v t))) '(b a c))
(check= (get-pxvars (list (list nil '^ t) '^ (list nil '^ t))) '())


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; del: Any x list -> list
;; Del removes the first instance of an element e in list l
(defunc del (e l)
  :input-contract (listp l)
  :output-contract (listp (del e l))
  (cond ((endp l) l)
        ((equal e (first l)) (rest l))
        (t (cons (first l) (del e (rest l))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; perm: list x list -> boolean
;; We define perm (permutation) to make the tests more robust. Otherwise, 
;; some of the tests below may fail because the order in which variables appear
;; does not matter.
(defunc perm (a b)
  :input-contract (and (listp a) (listp b))
  :output-contract (booleanp (perm a b))
  (cond ((endp a) (endp b))
        ((endp b) nil)
        (t (and (in (first a) b)
                (perm (rest a) (del (first a) b))))))

(test? (implies (and (listp p) (listp q)(listp r))
                (perm (app (app p q) r) (app (app r q) p))))

;; Add Your Own Tests
(defconst *pxtest1* 'A)
(defconst *pxtest2* '(A ^ (B v A)))
(defconst *pxtest3* '((A ^ B) ^ (C v D)))


(check= (perm (get-pxvars *pxtest1*) '(A)) t)
(check= (perm (get-pxvars *pxtest2*) '(A B)) t)
(check= (perm (get-pxvars *pxtest3*) '(D C B A)) t)
(check= (perm (get-pxvars *pxtest2*) '(B A)) t)

(check= (perm (get-pxvars (list (list 'a '^ 'b) '^  (list 'c '^ 'd))) 
              '(a b c d)) t)
(check= (perm (get-pxvars (list (list 'a '^ 'b) '^  (list 'c '^ 'd))) 
              '(a b c d d)) nil)
(check= (perm (get-pxvars (list (list 'a '^ 'b) '^ (list (list '~ 'c) 'v t))) 
              '(a d c)) nil)
(check= (perm (get-pxvars (list nil '^  (list 'c '^ 'd))) '(d c)) t)
(check= (perm (get-pxvars (list nil '^  (list 'c '^ 'd))) '(d d)) nil)
(check= (perm (get-pxvars (list nil '^  nil)) '(d c)) nil)
(check= (perm (get-pxvars (list nil '^  nil)) nil) t)
(check= (perm (get-pxvars (list (list t '^ nil) '^ (list (list '~ t) 'v t))) 
              '(a d c)) nil)
(check= (perm (get-pxvars (list (list t '^ nil) '^ (list (list '~ t) 'v t))) 
              '()) t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; update: PropEx x Symbol x Boolean -> PropEx
; The update function "updates a variable" by replacing all instances
; of the variable with the boolean val in the expression px.
; This is a DOUBLE RECURSION function.  I've implemented it for you to
; demonstrate what I mean and hopefully make get-pxvars (above) easier to write.
(defunc update (px name val)
  :input-contract (and (PropExp px) (symbolp name) (booleanp val))
  :output-contract (Propexp (update px name val))
  (cond ((equal px name)                 val)
        ((or (symbolp px) (booleanp px)) px)
        ((equal (len px) 2)              (list (first px) (update (second px) name val)))
        (t                               (list (update (first px) name val) 
                                               (second px) (update (third px) name val)))))

(check= (update T 'A NIL) T)
(check= (update NIL 'A T) NIL)
(check= (update 'A 'B T) 'A)
(check= (update 'A 'A NIL) NIL)
(check= (update '((NIL v A) ^ (~ B)) 'A T) '((NIL v T) ^ (~ B)))

;;Write test? tests or theorems to validate your update code.
(test? (implies (and (PropExp px)
                     (symbolp name)
                     (booleanp val))
                (equal (len px) (len (update px name val)))))
(test? (implies (and (PropExp px)
                     (symbolp name)
                     (booleanp val))
                (not (in name (len (update px name val))))))
(test? (implies (and (PropExp px)
                     (and (prop-varp name)
                          (in name px))
                     (booleanp val))
                (equal (- (len (get-pxvars px)) 1)
                       (len (get-pxvars (update px name val))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; BoolExp: All -> Boolean
;; (BooleanExp px) determines if px is a PropEx 
;; with NO symbols / free variables. Therefore
;; '(t ^ nil) returns true but '(t v A) returns nil.
(defunc BoolExp (px)
  :input-contract t
  :output-contract (booleanp (BoolExp px))
  (if (propExp px)
    (equal (len (get-pxvars px)) 0)
    nil)) 

(test? (implies (not (propExp px))
                (equal nil (boolexp px))))

(test? (implies (and (propExp px)
                     (equal (len (get-pxvars px)) 0))
                (equal t (boolexp px))))

(test? (implies (and (propExp px)
                     (< 0 (len (get-pxvars px))))
                (equal nil (boolexp px))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; beval: PropEx -> Booleanp
; TO ADD
; (beval bx)evaluates a constant boolean expression (bx) and 
;; returns its value.  
; A constant boolean expression is a PropEx with no variables, 
; just booleans and operators.
; You should add how  you handle each of the binary connectors
; so that the correct value is returned.
(defunc beval (bx)
  :input-contract (BoolExp bx)
  :output-contract (booleanp (beval bx))
  (if (booleanp bx) 
    bx
    (if (atom bx) 
      t
      (if (UnaryOpp (first bx))
        (not (beval (second bx)))
        (let ((first-beval (beval (first bx)))
              (third-beval (beval (third bx))))
          (cond
           ((equal (second bx) '^)  (and first-beval third-beval))
           ((equal (second bx) 'v)  (or first-beval third-beval))
           ((equal (second bx) '=>) (implies first-beval third-beval))
           ((equal (second bx) '==) (iff first-beval third-beval))
           ((equal (second bx) '<>) (or 
                                     (and (not first-beval) third-beval)
                                     (and first-beval (not third-beval))))))))))
           
(check= (beval T) T)
(check= (beval NIL) NIL)
(check= (beval '(T ^ NIL)) NIL)
(check= (beval '(T ^ T)) T)
;; Add additional tests
(check= (beval (list (list 'T '^ 'NIL) '<> 'NIL)) NIL)
(check= (beval (list (list 'T '^ 'T) '<> 'NIL)) T)
(check= (beval (list 'T '^ 'T)) T)
(check= (beval (list 'T '^ 'NIL)) NIL)
(check= (beval (list 'NIL '^ 'T)) NIL)
(check= (beval (list 'NIL '^ 'NIL)) NIL)
(check= (beval (list 'T 'v 'T)) T)
(check= (beval (list 'T 'v 'NIL)) T)
(check= (beval (list 'NIL 'v 'T)) T)
(check= (beval (list 'NIL 'v 'NIL)) NIL)
(check= (beval (list 'T '<> 'T)) NIL)
(check= (beval (list 'T '<> 'NIL)) T)
(check= (beval (list 'NIL '<> 'T)) T)
(check= (beval (list 'NIL '<> 'NIL)) NIL)
(check= (beval (list 'T '=> 'T)) T)
(check= (beval (list 'T '=> 'NIL)) NIL)
(check= (beval (list 'NIL '=> 'T)) T)
(check= (beval (list 'NIL '=> 'NIL)) T)
(check= (beval (list 'T '== 'T)) T)
(check= (beval (list 'T '== 'NIL)) NIL)
(check= (beval (list 'NIL '== 'T)) NIL)
(check= (beval (list 'NIL '== 'NIL)) T)
(check= (beval '(~ nil)) T)
(test? (implies (and (BoolExp bx)
                     (listp bx)
                     (equal (len bx) 2))
                (equal (not bx)
                       (beval bx))))

;; Temporarily switching back to logic mode to accept 
;; new data definitions
:logic
;; DEFINE a list of boolean expression PAIRS that can be evaluated.
(defdata px-pair (list propex propex))
;; Define a list of px-pairs 
(defdata lopxp (listof px-pair))

:program

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; boolExListp: t -> boolean
;;
;; (boolExListp l) is a recognizer that determines
;; if l is a list of px-pairs and if each of these
;; pairs evaluate to the same value.  The list of 
;; px-pairs constitutes what a pair of prop expressions
;; look like with each variable replaced with a boolean.
(defunc boolExListp (l)
  :input-contract t
  :output-contract (booleanp (boolExListp l))
  (if (lopxpp l)
    (if (endp l)
      t
      (and (BoolExp (first (first l)))
           (BoolExp (second (first l)))
           (boolExListp (rest l))))
    nil))
      

(defconst *bx1* '(t <> t))
(defconst *bx2* '((t ^ nil) v t))
(defconst *bx3* '((t ^ nil) v t))
(defconst *bx4* '((t == nil) => nil))
(defconst *px-test-list* (list (list *bx1* *bx2*)
                               (list *bx1* *bx3*)
                               (list *bx4* *bx4*)
                               (list *bx1* *bx1*)))

(defconst *px-test2-list* (list (list *bx1* *bx1*)
                                (list *bx2* *bx2*)
                                (list *bx4* *bx4*)
                                (list *bx3* *bx3*)))

(check= (BoolExp *bx1*) t)
(check= (get-pxvars *bx1*) nil)
(check= (BoolExp *bx2*) t)

(check= (lopxpp *px-test-list*) t)
(check= (lopxpp *px-test2-list*) t)
(check= (boolExListp *px-test-list*) t)
(check= (boolExListp *px-test2-list*) t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; px-assign-list=: BoolExList -> booleanp
;; (px-assign-list= l) takes a boolean expression list
;; (each expression has no variables) and determines 
;; if the pairs of boolean expressions are equivalent
;; for each pair in the list.
(defunc px-assign-list= (l)
  :input-contract (boolExListp l)
  :output-contract (booleanp (px-assign-list= l))
  (if (endp l)
    t
    (let ((pxpair1 (first (first l)))
          (pxpair2 (second (first l))))  
      (and (equal (beval pxpair1)(beval pxpair2))
           (px-assign-list= (rest l))))))

(check= (px-assign-list= *px-test-list*) nil)
(check= (px-assign-list= *px-test2-list*) t) 
(cons (list t (list '~ 'a)) (list (list nil)))
(lopxpp (cons (list t (list '~ 'a)) (list (list nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; gen-sat-list: PropEx x PropEx x Lov -> Lopxp
;; Suggested helper method. Takes two propositional expressions (px1 and px2)
;; and the list of variables (vars) contained in either expression and generates 
;; a list of PropExs representing each truth table row.
;; px1 & px2: the expressions (to have variables replaced)
;; Hint: Replace all variables in px1 and px2 in a methodical way and 
;; determine if it's true using beval.  Try T and nil for all variables 
;; (found in vars). Let can help simplify your code. You may also think
;; about trying to just replace all variables with t in both expressions
;; Then you can try double recursion
(defunc gen-assign-list-pairs (px1 px2 vars)
  :input-contract (and (PropExp px1) (PropExp px2) (Lovp vars))
  :output-contract (lopxpp (gen-assign-list-pairs px1 px2 vars))
    (if (endp vars)
      (list (list px1 px2))
      (let* ((upd-px1 (update px1 (first vars) t))
             (upd-px2 (update px2 (first vars) t))
             (updn-px1 (update px1 (first vars) nil))
             (updn-px2 (update px2 (first vars) nil)))
        (append (gen-assign-list-pairs upd-px1 upd-px2 (rest vars))
                (gen-assign-list-pairs updn-px1 updn-px2 (rest vars))))))

(check= (gen-assign-list-pairs 'a t '(a)) (list (list t t)
                                                (list nil t)))
(check= (gen-assign-list-pairs '(a v b) t '(a b)) (list (list (list t 'v t) t)
                                                        (list (list t 'v nil) t)
                                                        (list (list nil 'v t) t)
                                                        (list (list nil 'v nil) t)))  

;; Write your own tests.  The constants below can be used but you should
;; try your own.
(defconst *pxtest1* 'A)
(defconst *pxtest2* '(A ^ (B v A)))
(defconst *pxtest3* '((A ^ B) ^ (C v D)))
(defconst *pxtest4* '(A => (A <> A)))
(defconst *pxtest5* '(~ T))
(defconst *pxtest6* T)
(defconst *pxtest7* '((A ^ E) ^ (F ^ D)))

(check= (gen-assign-list-pairs *pxtest2* *pxtest4* '(A B))
        (list (list '(t ^ (t v t)) '(t => (t <> t)))
              (list '(t ^ (nil v t)) '(t => (t <> t)))
              (list '(nil ^ (t v nil)) '(nil => (nil <> nil)))
              (list '(nil ^ (nil v nil)) '(nil => (nil <> nil)))))
        
(gen-assign-list-pairs *pxtest3* *pxtest2* '(A B C D))
(check= (gen-assign-list-pairs *pxtest4* *pxtest5* '(A))
        (list (list '(t => (t <> t)) '(~ t))
              (list '(nil => (nil <> nil)) '(~ t))))
(test? (implies (and (PropExp px1)(PropExp px2) (Lovp vars))
                (boolExListp (gen-assign-list-pairs px1 px2 
                                                    (merge-nodups (get-pxvars px1)
                                                                  (get-pxvars px2))))))
(test? (implies (and (and (PropExp px1)
                          (not (booleanp px1)))
                     (and (PropExp px2)
                          (not (booleanp px2)))
                     (and (Lovp vars)(not (perm vars
                                           (merge-nodups (get-pxvars px1)(get-pxvars px2))))))
                (not (boolExListp (gen-assign-list-pairs px1 px2 
                                                    (merge-nodups (get-pxvars px1)
                                                                  (get-pxvars px2)))))))
                

;; This shows what happens if all variables are not removed.
;; px-assign-list= cannot be called
(check= (boolExListp (gen-assign-list-pairs *pxtest3* *pxtest2* '(A B))) nil) 

(check= (px-assign-list= (gen-assign-list-pairs *pxtest1* *pxtest4* '(a))) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFINE
;; propEx= PropEx x PropEx -> Boolean
;; (propEx= px1 px2) takes two propositional expressions
;; px1 and px2 and returns true if all possible variable
;; assignments for the expressions lead to the same result
;; Else return nil.
;; Look for how we can compare lists px assignment pairs, how
;; we get px vars and how we can remove duplicate variables.
(defunc propEx= (px1 px2)
  :input-contract (and (PropExp px1)(PropExp px2))
  :output-contract (booleanp (propEx= px1 px2))
  (px-assign-list= 
   (gen-assign-list-pairs px1 px2 (merge-nodups (get-pxvars px1)(get-pxvars px2)))))

  
;; Just test code so you can see all the results generated for
;; a pair of variable free propositional expressions.
(defunc px-assign-list-val (l)
  :input-contract (boolExListp l)
  :output-contract (listp (px-assign-list-val l))
  (if (endp l)
    nil
    (let ((pxpair1 (first (first l)))
          (pxpair2 (second (first l))))  
      (cons (list (beval pxpair1)(beval pxpair2))
            (px-assign-list-val (rest l))))))

(px-assign-list-val (gen-assign-list-pairs *pxtest2* *pxtest4* '(A B)))
(px-assign-list-val (gen-assign-list-pairs *pxtest1* *pxtest4* '(A)))
(px-assign-list-val (gen-assign-list-pairs *pxtest1* *pxtest2* '(A B)))
(px-assign-list-val (gen-assign-list-pairs *pxtest5* *pxtest6* nil))
(px-assign-list-val (gen-assign-list-pairs *pxtest3* *pxtest2* '(A B C D)))

(merge-nodups (get-pxvars *pxtest5*) (get-pxvars *pxtest6*))


(check= (propEx= *pxtest1* *pxtest4*) nil) ;; A vs ~A
(check= (propEx= *pxtest1* *pxtest2*) t) ;; Both resolve to A
(check= (propEx= *pxtest5* *pxtest6*) nil) ;; T vs nil
(check= (propEx= *pxtest3* *pxtest2*) nil) ;; variables C and D are important
;; Add your own tests to ensure that propEx= works as expected.
(check= (propEx= *pxtest6* *pxtest6*) t)
(check= (propEx= (not *pxtest6*) (not *pxtest6*)) t)
(check= (propEx= (not *pxtest6*) *pxtest6*) nil)
(test? (implies (and (booleanp px1)
                     (booleanp px2))
                (equal (equal px1 px2)
                       (propEx= px1 px2))))#|ACL2s-ToDo-Line|#




