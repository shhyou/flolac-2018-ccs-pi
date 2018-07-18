#lang racket

(require racket/syntax
         "ccs-pi-language.rkt"
         "utils.rkt"
         redex/reduction-semantics)

;; Tools for running examples
(define (lex-order rule-name)
  (cond [(equal? rule-name "Rep") 0]
        [(equal? rule-name "Res Par") -1]
        [else -2]))

(define (ccs-sort-rule name1 name2)
  (define l1 (lex-order name1))
  (define l2 (lex-order name2))
  (or (< l1 l2)
      (and (= l1 l2) (string<? name1 name2))))

(define/match (ccs-consume-fuel next-step fuel)
  [((list rule-name t-next) fuel)
   (cond [(member rule-name '("Rep" "Res Res")) (- fuel 1)]
         [else fuel])])

(define (ccs-run fuel t)
  (run-many fuel R t
            #:verbose? #t
            #:use-fuel ccs-consume-fuel
            #:compare ccs-sort-rule))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Some examples
(define communication-example
  (term (‖ (a (x) (x ⇐ c))
           (a ⇐ b))))

(define scope-extrusion-example
  (term (‖ (ν (b) (a ⇐ b))
           (a (x)
              (c ⇐ x)))))

;; Small agents
(define-metafunction CCS
  FW : a b -> P
  [(FW a b) (a (z) (b ⇐ z))])

(define-metafunction CCS
  D : a b c -> P
  [(D a b c) (a (z)
                (‖ (b ⇐ z)
                   (c ⇐ z)))])

(define-metafunction CCS
  K : a -> P
  [(K a) (a (z) nil)])

(define-metafunction CCS
  NN : a -> P
  [(NN a) (! (a (x)
                (ν (b) (x ⇐ b))))])

;; Hacking!
(define-metafunction CCS+eval
  [(SClient- integer)
   (ν (c) (‖ (a ⇐ c)
             (c (x) (abstract-function c x))))
   (where/error abstract-function ,(format-symbol "PClient~a" (term integer)))])

(define-term SServer
  (! (a (z)
        (ν (s)
           (‖ (z ⇐ s)
              (PServer z s))))))

(define secure-client-server-example
  (term (‖ (SClient- 1) (SClient- 2) SServer)))

(define synchronous-communication-example1
  (term (‖ (send/sync (a ⇐ c)
                      (Sender1))
           (send/sync (a ⇐ d)
                      (Sender2))
           (recv/sync a (x)
                      (Recv x)))))

(define synchronous-communication-example2
  (term (‖ (send/sync (a ⇐ c d e f)
                      (Sender))
           (recv/sync a (x y z w)
                      (Recv x y z w)))))

(define branching-example1
  (term (‖ (! (a (x)
                 (▹ x
                    [read (ReadReply x)]
                    [write (recv/sync x (w) (WriteReply x w))])))
           (ν (sa)
              (‖ (a ⇐ sa)
                 (◃ sa (read ∈ (read write))
                    (ReadRequest sa))))
           (ν (sb)
              (‖ (a ⇐ sb)
                 (◃ sb (write ∈ (read write))
                    (send/sync (sb ⇐ c)
                               (WriteRequest sb))))))))
