#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics)

(define-language CCS
  ;; channels
  [a b c d e ::=
     (variable-prefix a) (variable-prefix b) (variable-prefix c) (variable-prefix d)
     (variable-prefix e) (variable-prefix f) (variable-prefix g) (variable-prefix s)
     (variable-prefix t) (variable-prefix q) (variable-prefix r)]

  ;; variables
  [x y z w ::=
     (variable-prefix x) (variable-prefix y) (variable-prefix z) (variable-prefix w)]
  [u v ::= a x]

  ;; processes
  [P Q ::=
     nil
     (‖ P ...)
     ((ν a) P)
     (! P)
     (u ⇐ v) ;; maybe use (▔ u ⟨ v ⟩) instead?
     (u (x) · P)]
  #:binding-forms
  ((ν a) P #:refers-to a)
  (u (x) · P #:refers-to x))

(define-extended-language CCS+eval CCS
  [abstract-function
   (variable-prefix A) (variable-prefix B) (variable-prefix C) (variable-prefix D)
   (variable-prefix E) (variable-prefix F) (variable-prefix G) (variable-prefix H)
   (variable-prefix I) (variable-prefix J) (variable-prefix K) (variable-prefix L)
   (variable-prefix M) (variable-prefix N) (variable-prefix O) (variable-prefix P)
   (variable-prefix Q) (variable-prefix R) (variable-prefix S) (variable-prefix T)
   (variable-prefix U) (variable-prefix V) (variable-prefix W) (variable-prefix X)
   (variable-prefix Y) (variable-prefix Z)]
  [P ::= .... (abstract-function u v ...)]
  [E ::=
     hole
     (‖ P ... E Q ...)
     ((ν a) E)])

(define R
  (reduction-relation
   CCS+eval
   #:domain P

   ;; unfolding
   (--> (in-hole E (! P))
        (in-hole E (‖ P (! P)))
        "Rep")

   ;; congruence (2)
   (--> (in-hole E (par))
        (in-hole E nil)
        "Par Nil")
   (--> (in-hole E (‖ P ... nil Q ...))
        (in-hole E (‖ P ... Q ...))
        "Zero")
   (--> (in-hole E (‖ P_1 ... (‖ Q ...) P_2 ...))
        (in-hole E (‖ P_1 ... Q ... P_2 ...))
        "Assoc")

   ;; congruence (3)
   (--> (in-hole E ((ν a) nil))
        (in-hole E nil)
        "Res Nil")

   ;; No need to include this congruence rule
   #;
   (--> (in-hole E ((ν a) ((ν b) P)))
        (in-hole E ((ν b) ((ν a) P)))
        "Res Res")

   (--> (in-hole E (‖ P_1 ... ((ν a) Q) P_2 ...))
        (in-hole E ((ν a) (‖ P_1 ... Q P_2 ...)))
        "Res Par")

   ;; communication!
   (--> (in-hole E (‖ P_1 ... (a ⇐ v) P_2 ... (a (x) · P) P_3 ...))
        (in-hole E (‖ P_1 ... P_2 ... (substitute P x v) P_3 ...))
        "Comm1")
   (--> (in-hole E (‖ P_1 ... (a (x) · P) P_2 ... (a ⇐ v) P_3 ...))
        (in-hole E (‖ P_1 ... P_2 ... (substitute P x v) P_3 ...))
        "Comm2")
   ))
