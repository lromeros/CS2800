; **************** BEGIN INITIALIZATION FOR ACL2s BB MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.

Pete Manolios
Thu Jan 20 08:50:00 EST 2011
----------------------------

The idea of the Bare Bones level is to introduce ACL2 as a
programming language with contracts (a "typed" ACL2) to the
students, using a "minimal" subset of primitive functions.
For example, in the case of the Booleans, all that is built-in
are the constants t and nil and the functions if and equal.

Everything else is built on top of that. 

|#

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Bare Bones mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s bare-bones theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "bare-bones-theory" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Bare Bones mode.") (value :invisible))

;Settings specific to ACL2s Bare Bones mode.
(acl2s-bare-bones-settings)
(acl2::xdoc acl2s::defunc)

(cw "~@0Bare Bones mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")

(acl2::in-package "ACL2S BB")


; ***************** END INITIALIZATION FOR ACL2s BB MODE ******************* ;

;$ACL2s-SMode$;Bare Bones

t
; t is the Boolean constant denoting true

nil 

; nil is the Boolean constant denoting false

3
; the integer 3

-12
; the integer 12

-2/3
; the rational 

-212/72
; notice acl2s simplified rationals

(if t nil t)
; an if statement

(if nil 3 4)
; another if statement

(defunc booleanp (x)
  :input-contract t
  :output-contract (booleanp (booleanp x))
  (if (equal x t)
    t
    (equal x nil)))

; a function definition
; the input contract tells us under what conds the 
; the t is always true. doesn't even depend on the 
; booleanp can take any yvalue as input.
; the output contract tellsuse the type that the function should retunr
;

(defunc and (a b)
  :input-contract (if (booleanp a) (booleanp b) nil)
  :output-contract (booleanp (and a b))
  (if a b nil))

; Next define and, implies, andor