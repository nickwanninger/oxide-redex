#lang racket

(require redex/reduction-semantics)
(require rackunit)



(define-language Simple
  ;; Expressions
  (e ::=

     ;; Terminals.
     c
     p

     ;; Reference acquisition.
     (& r ω x)

     ;; Variable binding.
     (letvar x : t = e e) ;; bind x of type τ to the result of e, place at ρ
     ;; (x : t = e)

     ;; Region binding.
     (letrgn [r] e)
     
     ;; Structured control flow
     (if e e e)   ;; predication, "the only interesting thing"
     ;;                             -Christos Dimoulas, Ph.D.
     ;;                               5/9/2024
     )

  ;; Constants
  (c ::= i true false ())
  (i ::= integer)
  
  ;; Place expressions.
  (p ::=
     x     ;; variable
     (* p) ;; dereference
     ;; (. p i) ;; tuple indexing
     )

  ;; Variables.
  (x ::= variable-not-otherwise-mentioned)

  ;; Region
  (ρ ::=
     r ;; concrete region
     ϱ ;; abstract region
     )
  ;; Concrete region variables.
  (r ::= variable-not-otherwise-mentioned)
  ;; Abstract region variables.
  (ϱ ::= variable-not-otherwise-mentioned)


  ;; Ownership qualifiers.
  (ω ::= shared unique)

  ;; Types
  (t ::=
     unit      ;; unit type
     int       ;; integer type
     bool      ;; boolean type
     (& ρ ω t) ;; reference type

     ;; α              ;; type variable
     ;; ((t ...) -> t) ;; function type
     )


  #:binding-forms
  (letvar x : t = e e #:refers-to x)
  (letrgn [r] e #:refers-to r)
  )

(default-language Simple)

;; Extended language for the typechecker.
(define-extended-language Simple+Γ Simple
  (Γ  ::= (Γv Γr))
  (Γv ::= ((x : t) ...))
  (Γr ::= ((r ↦ loans) ...))
  (loans ::= {(ω p) ...})
      
               
  )

(define-judgment-form Simple+Γ
  #:mode (⊢ I I O O)
  #:contract (⊢ Γ e t Γ) ;; Take Γ and e, produce t (type of e) and new Γ

  [-------------- "unit"
   (⊢ Γ () unit Γ)]
  
  [-------------- "integer"
   (⊢ Γ integer int Γ)]

  [--------------- "bool true"
   (⊢ Γ true bool Γ)]

  [--------------- "bool false"
   (⊢ Γ false bool Γ)]

  [----------------------- "variable"
   (⊢ Γ x (lookup-var x Γ) Γ)]

  [ ;; TODO: the hard part :3
   ;; Γ(r) = ∅
   ;; Γ ⊢ω p => { ℓ }
   ;; Γ ⊢ω p : t
   (⊢ Γ x t Γ_x)
   ----------------- "borrow"
   (⊢ Γ (& r ω x) (& r ω t) Γ)]

  [(⊢ Γ e_bind t_bind Γ_bind)
   (⊢ (extend-var x t Γ) e_body t_body Γ_body)
   ----------------------------------------------- "variable declaration"
   (⊢ Γ (letvar x : t = e_bind e_body) t_body Γ)]

  ;; [(⊢ Γ e t Γ_e)
  ;;  ---------------------- "variable definition"
  ;;  (⊢ Γ (x : t = e) unit Γ)]
  
  [(⊢ (extend-rgn r {} Γ) e t Γ_e)
   ---------------------------------------- "region binding"
   (⊢ Γ (letrgn [r] e) t (drop-rgn r Γ_e))]
  
  )

(define-metafunction Simple+Γ
  [(same? t_1 t_1) #t]
  [(same? t_1 t_2) #f]
  )

(define-metafunction Simple+Γ
  extend-var : x t Γ -> Γ
  [(extend-var x t (((x_Γ : t_Γ) ...) Γr))
   (((x : t) (x_Γ : t_Γ) ...) Γr)]
  )

(define-metafunction Simple+Γ
  lookup-var : x Γ -> t
  [(lookup-var x
               (((x : t) (x_2 : t_2) ...) Γr))
   t]
  [(lookup-var x
               (((x_1 : t_1) (x_2 : t_2) ...)
                Γr))
   (lookup-var x
               (((x_2 : t_2) ...)
                Γr))]
  )

(define-metafunction Simple+Γ
  extend-rgn : r loans Γ -> Γ
  [(extend-rgn r loans (Γv ((r_Γ ↦ loans_Γ) ...)))
   (Γv ((r ↦ loans) (r_Γ ↦ loans_Γ) ...))]
  )

(define-metafunction Simple+Γ
  lookup-rgn : x Γ -> t
  [(lookup-rgn r
               (Γv
                ((r ↦ loans) (r_2 ↦ loans_2) ...)))
   loans]
  [(lookup-rgn r (Γv ((r_1 ↦ loans_1) (r_2 ↦ loans_2) ...)))
   (lookup-rgn r (Γv ((r_2 ↦ loans_2) ...)))]
  )

  (define-metafunction Simple+Γ
    drop-rgn : r Γ -> Γ
    [(drop-rgn r (Γv ((r ↦ loans) (r_Γ ↦ loans_Γ) ...)))
     (Γv ((r_Γ ↦ loans_Γ) ...))]
    [(drop-rgn r (Γv ((r_other ↦ loans_other) (r_Γ ↦ loans_Γ) ...)))
     (drop-rgn r (Γv ((r_Γ ↦ loans_Γ) ...)))]
   )

;; Tests for the typechecker.
(define-term Γ_empty (() ()))
(test-judgment-holds (⊢ Γ_empty 1 int any))
(test-judgment-holds (⊢ Γ_empty true bool any))
(test-judgment-holds (⊢ Γ_empty false bool any))
(test-judgment-holds (⊢ Γ_empty (letvar x : int = 1 x) int any))
(test-judgment-holds (⊢ Γ_empty (letvar x : bool = false x) bool any))
(test-judgment-holds (⊢ Γ_empty
                        (letvar x : bool = false (letvar y : bool = true x))
                        bool
                        any))

(test-equal
 (judgment-holds (⊢ Γ_empty (letvar x : int = false x) bool any))
 #false)

;; References
(test-judgment-holds (⊢ Γ_empty
                        (letvar x : int = 0
                                (letrgn [r1] (& r1 unique x)))
                        (& r unique int)
                        any))

(test-results)
