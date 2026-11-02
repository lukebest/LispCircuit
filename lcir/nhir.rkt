#lang racket
;; Normalized hardware IR. Rules have been lowered to per-resource
;; write-enables and next-state muxes. Hierarchy is still intact.

(require "ast.rkt" "types.rkt")
(provide (struct-out hmod)
         (struct-out hport)
         (struct-out hreg)
         (struct-out hwire)
         (struct-out htable)
         (struct-out hinst)
         (struct-out hside)
         hmod-port
         hmod-alias
         hmod-input-names
         hmod-output-names)

(struct hmod (name kind params clocks ports aliases regs wires tables insts sides info)
  #:transparent)
(struct hport (name dir ty info) #:transparent)
(struct hreg (name ty init reset-less? clock we next mode guards info) #:transparent)
(struct hwire (name ty expr info) #:transparent)
(struct htable (name depth elem-ty latency clock wen waddr wdata ren raddr info) #:transparent)
(struct hinst (name mod connects info) #:transparent)
(struct hside (guard kind data info) #:transparent)

(define (hmod-port h name)
  (findf (lambda (p) (eq? (hport-name p) name)) (hmod-ports h)))

(define (hmod-alias h name)
  (findf (lambda (a) (eq? (salias-name a) name)) (hmod-aliases h)))

(define (hmod-input-names h)
  (for/list ([p (hmod-ports h)] #:when (eq? (hport-dir p) 'in))
    (hport-name p)))

(define (hmod-output-names h)
  (for/list ([p (hmod-ports h)] #:when (eq? (hport-dir p) 'out))
    (hport-name p)))
