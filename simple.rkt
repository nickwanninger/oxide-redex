#lang racket

(require redex/reduction-semantics)
(require rackunit)



(define-language Simple
  ;; Expressions
  (e ::=

     ;; Terminals.
     c
     x

     ;; Variable binding.
     (letvar x @ p : t = e) ;; bind x of type τ to the result of e, place at ρ

     ;; Region binding.
     (letrgn [r] e)
     
     ;; Structured control flow
     (do e e ...) ;; sequencing, racket doesnt like ;
     ;; (if e e e)   ;; predication
     ;; (while e e)  ;; recursion
     )


  ;; Types
  (t ::=
     ()             ;; unit type
     int            ;; integer type
     bool           ;; boolean type
     ;; ((t ...) -> t) ;; function type
     )
  
  ;; Regions
  (p ::= r)

  ;; Ownership qualifiers.
  (ω ::= shrd uniq)

  ;; Constants
  (c ::= i b)
  (i ::= integer)
  (b ::= true false)
  
  ;; Variables.
  (x ::= variable-not-otherwise-mentioned)
  ;; Region variables.
  (r ::= variable-not-otherwise-mentioned)

  #:binding-forms
  (letvar x @ p : t = e #:refers-to x)
  (letrgn [r] e #:refers-to r)
  
  )

(default-language Simple)

;; Extended language for the typechecker.
(define-extended-language Simple-tc Simple
  (Γ ::= ((x t) ...))
  )

(define-judgment-form Simple-tc
  #:mode (⊢ I I O O)
  #:contract (⊢ Γ e Γ t) ;; Take Γ and e, produce t (type of e) and new Γ

  [-------------- "int"
   (⊢ Γ i Γ int )]

  [--------------- "bool"
   (⊢ Γ b Γ bool)]

  [----------------------- "variable"
   (⊢ Γ x Γ (lookup Γ x))]

  [(⊢ Γ e Γ_e t)
   ------------------------------------------------ "variable binding"
   (⊢ Γ (letvar x @ p : t = e) (extend Γ (x t)) t)]

  [(⊢ Γ e Γ_e t)
   ------------------------- "region binding"
   (⊢ Γ (letrgn [p] e) Γ t)]
  
  [(⊢ Γ e Γ_e t_e)
   (⊢ Γ_e (do e_rest ...) Γ_rest t_rest)
   ------------------------------------- "sequencing"
   (⊢ Γ (do e e_rest ...) Γ_rest t_rest)]
  
  )

(define-metafunction Simple-tc
  extend : Γ (x t) -> Γ
  [(extend ((x_Γ t_Γ) ...) (x t)) ((x t) (x_Γ t_Γ) ...)]
  )

(define-metafunction Simple-tc
  lookup : Γ x -> t
  [(lookup ((x_1 t_1) ... (x t) (x_2 t_2) ...) x)
   t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2) ,(error 'lookup "not found : ~e" (term x))]
  )

;; Tests for the typechecker.
(test-judgment-holds (⊢ () 1 any int))
(test-judgment-holds (⊢ () true any bool))
(test-judgment-holds (⊢ () false any bool))
(test-judgment-holds (⊢ () (letvar x @ p : int = 1) any int))
(test-judgment-holds (⊢ () (letvar x @ p : bool = false) any bool))

(test-equal
 (judgment-holds (⊢ () (letvar x @ p : int = false) any int))
 #false)

(test-equal
 (judgment-holds (⊢ () (letvar x @ p : int = false) any bool))
 #false)

(test-results)
