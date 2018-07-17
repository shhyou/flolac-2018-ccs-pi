#lang racket

(provide (all-defined-out))

(require redex/reduction-semantics
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
  [P ::= .... (abstract-function u ...)]
  [E ::=
     hole
     (‖ P ... E Q ...)
     ((ν a) E)])

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
  [(fn ((ν a) P)) (set-remove (fn P) a)]
  [(fn (! P)) (fn P)]
  [(fn (u ⇐ v))
   (a_free ... ...)
   (where/error ((a_free ...) ...) ((fn-var u) (fn-var u)))]
  [(fn (u (x) · P)) (fn P)]
  [(fn (abstract-function u ...))
   (a_free ... ...)
   (where/error ((a_free ...) ...) ((fn-var u) ...))])

(define-metafunction CCS+eval
  fv : P -> (x ...)
  [(fv nil) ()]
  [(fv (‖ P ...))
   (x_free ... ...)
   (where/error ((x_free ...) ...) ((fv P) ...))]
  [(fv ((ν a) P)) (fv P)]
  [(fv (! P)) (fv P)]
  [(fv (u ⇐ v))
   (x_free ... ...)
   (where/error ((x_free ...) ...) ((fv-var u) (fv-var u)))]
  [(fv (u (x) · P)) (set-subtract (fv P) x)]
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
   (--> (in-hole E ((ν a) nil))
        (in-hole E nil)
        "Res Nil")

   ;; Res Nil combined with other rules -- see Question 1 in the slide
   (--> (in-hole E ((ν a) P))
        (in-hole E P)
        (side-condition (not (member (term a) (term (fn P)))))
        "Res Nil*")

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

;; encoding synchronous communication in asynchronous π-calculus
(define-metafunction CCS+eval
  send/sync : u ⇐ v · P -> P
  [(send/sync u ⇐ v · P)
   ((ν s)
    (‖ (u ⇐ s)
       (s (z) ·
          (‖ (z ⇐ v)
             P))))
   (where/error s ,(variable-not-in (term (u v P)) 's))
   (where/error z ,(variable-not-in (term (u v P)) 'z))])

(define-metafunction CCS+eval
  recv/sync : u (x) · P -> P
  [(recv/sync u (x) · P)
   (u (z) ·
      ((ν s)
       (‖ (z ⇐ s)
          (s (x) · P))))
   (where/error s ,(variable-not-in (term (u x P)) 's))
   (where/error z ,(variable-not-in (term (u x P)) 'z))])

(define-metafunction CCS+eval
  do-send*/sync : u ⇐ v ... · P -> P
  [(do-send*/sync u ⇐ v · P)           (send/sync u ⇐ v · P)]
  [(do-send*/sync u ⇐ v_1 v_2 ... · P) (send/sync u ⇐ v_1 ·
                                                  (do-send*/sync u ⇐ v_2 ... · P))])

(define-metafunction CCS+eval
  do-recv*/sync : u (v ...) · P -> P
  [(do-recv*/sync u (v) · P)           (recv/sync u (v) · P)]
  [(do-recv*/sync u (v_1 v_2 ...) · P) (recv/sync u (v_1) ·
                                                  (do-recv*/sync u (v_2 ...) · P))])

(define-metafunction CCS+eval
  send*/sync : u ⇐ v ... · P -> P
  [(send*/sync u ⇐ v ... · P)
   ((ν s) (‖ (u ⇐ s)
             (do-send*/sync s ⇐ v ... · P)))
   (where/error s ,(variable-not-in (term (u v ... P)) 's))])

(define-metafunction CCS+eval
  recv*/sync : u (v ...) · P -> P
  [(recv*/sync u (v ...) · P)
   (u (z) · (do-recv*/sync z (v ...) · P))
   (where/error z ,(variable-not-in (term (u v ... P)) 'z))])
