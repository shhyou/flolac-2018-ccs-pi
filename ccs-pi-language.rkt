#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics
         racket/syntax
         "utils.rkt")

(define-language CCS
  ;; channels
  [a b c d e s ::=
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
     (ν (a ...) P)
     (! P)
     (u ⇐ v ...)
     (u (x ...) P)]
  #:binding-forms
  (ν (a ...) P #:refers-to (shadow a ...))
  (u (x ...) P #:refers-to (shadow x ...)))

(define-extended-language CCS+eval CCS
  [abstract-function
   (variable-prefix A) (variable-prefix B) (variable-prefix C) (variable-prefix D)
   (variable-prefix E) (variable-prefix F) (variable-prefix G) (variable-prefix H)
   (variable-prefix I) (variable-prefix J) (variable-prefix K) (variable-prefix L)
   (variable-prefix M) (variable-prefix N) (variable-prefix O) (variable-prefix P)
   (variable-prefix Q) (variable-prefix R) (variable-prefix S) (variable-prefix T)
   (variable-prefix U) (variable-prefix V) (variable-prefix W) (variable-prefix X)
   (variable-prefix Y) (variable-prefix Z)]
  [P ::= .... (abstract-function u ...)]
  [E ::=
     hole
     (‖ P ... E Q ...)
     (ν (a ...) E)])

;; Can't put this in utils.rkt since we need the binding
;; structure of CCS+eval here
(define-metafunction CCS+eval
  substitute* : any (any any) ... -> any
  [(substitute* any_term) any_term]
  [(substitute* any_term [any_old any_new] [any_olds any_news] ...)
   (substitute* (substitute any_term any_old any_new)
                [any_olds any_news]
                ...)])

(define-metafunction CCS+eval
  fn-var : u -> (a ...)
  [(fn-var a) (a)]
  [(fn-var x) ()])

(define-metafunction CCS+eval
  fv-var : u -> (x ...)
  [(fv-var a) ()]
  [(fv-var x) (x)])

(define-metafunction CCS+eval
  fn : P -> (a ...)
  [(fn nil) ()]
  [(fn (‖ P ...))
   (a_free ... ...)
   (where/error ((a_free ...) ...) ((fn P) ...))]
  [(fn (ν (a ...) P)) (set-subtract (fn P) (a ...))]
  [(fn (! P)) (fn P)]
  [(fn (u ⇐ v ...))
   (a_free ... ...)
   (where/error ((a_free ...) ...) ((fn-var u) (fn-var v) ...))]
  [(fn (u (x ...) P)) (fn P)]
  [(fn (abstract-function u ...))
   (a_free ... ...)
   (where/error ((a_free ...) ...) ((fn-var u) ...))])

(define-metafunction CCS+eval
  fv : P -> (x ...)
  [(fv nil) ()]
  [(fv (‖ P ...))
   (x_free ... ...)
   (where/error ((x_free ...) ...) ((fv P) ...))]
  [(fv (ν (a ...) P)) (fv P)]
  [(fv (! P)) (fv P)]
  [(fv (u ⇐ v ...))
   (x_free ... ...)
   (where/error ((x_free ...) ...) ((fv-var u) (fv-var v) ...))]
  [(fv (u (x ...) P)) (set-remove (fv P) (x ...))]
  [(fv (abstract-function u ...))
   (x_free ... ...)
   (where/error ((x_free ...) ...) ((fv-var u) ...))])

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
   (--> (in-hole E (ν (a ...) nil))
        (in-hole E nil)
        "Res Nil")

   ;; Res Nil combined with other rules -- see Question 1 in the slide
   (--> (in-hole E (ν (a ...) P))
        (in-hole E P)
        (side-condition (for/and ([a (in-list (term (a ...)))])
                          (not (member a (term (fn P))))))
        "Res Nil*")

   (--> (in-hole E (‖ P_1 ... (ν (a ...) Q) P_2 ...))
        (in-hole E (ν (a ...) (‖ P_1 ... Q P_2 ...)))
        "Res Par")

   ;; communication!
   (--> (in-hole E (‖ P_1 ... (a ⇐ v ..._arity) P_2 ... (a (x ..._arity) P) P_3 ...))
        (in-hole E (‖ P_1 ... P_2 ... (substitute* P [x v] ...) P_3 ...))
        "Comm1")

   (--> (in-hole E (‖ P_1 ... (a (x ..._arity) P) P_2 ... (a ⇐ v ..._arity) P_3 ...))
        (in-hole E (‖ P_1 ... P_2 ... (substitute* P [x v] ...) P_3 ...))
        "Comm2")
   ))

;; encoding synchronous communication in asynchronous π-calculus
(define-metafunction CCS+eval
  send/sync : (u ⇐ v ...) P -> P
  [(send/sync (u ⇐ v ...) P)
   (ν (s)
      (‖ (u ⇐ s)
         (s (z)
            (‖ (z ⇐ v ...)
               P))))
   (where/error s ,(variable-not-in (term (u v ... P)) 's))
   (where/error z ,(variable-not-in (term (u v ... P)) 'z))])

(define-metafunction CCS+eval
  recv/sync : u (x ...) P -> P
  [(recv/sync u (x ...) P)
   (u (z)
      (ν (s)
         (‖ (z ⇐ s)
            (s (x ...) P))))
   (where/error s ,(variable-not-in (term (u x ... P)) 's))
   (where/error z ,(variable-not-in (term (u x ... P)) 'z))])
