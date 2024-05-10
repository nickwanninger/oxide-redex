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

  [(⊢ (extend-rgn r {} Γ) e t Γ_e)
   ---------------------------------------- "region binding"
   (⊢ Γ (letrgn [r] e) t (drop-rgn r Γ_e))]


  ;; ⋓ requires that types of bound variables in the two stack
  ;; typings be equal (which potentially demands use of T-Drop when typing the branches), and unions
  ;; the loan sets for each region 𝑟 from both stack typings
  [(⊢ (Γv Γr) e_cond bool Γ_cond)
   (⊢ (Γv Γr) e_then t (Γv_then Γr_then))
   (⊢ (Γv Γr) e_else t (Γv_else Γr_else))
   ------------------------------------------------------- "branch"
   (⊢ (Γv Γr) (if e_cond e_then e_else) t (Γv (⋓ Γr_then Γr_else)))]
  
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
  insert-rgn : r loans Γr -> Γr
  [(insert-rgn r loans ((r_Γ ↦ loans_Γ) ...))
     ((r ↦ loans) (r_Γ ↦ loans_Γ) ...)]
  )

(define-metafunction Simple+Γ
  extend-rgn : r loans Γ -> Γ
  [(extend-rgn r loans (Γv Γr))
   (Γv (insert-rgn r loans Γr))]
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


(define-metafunction Simple+Γ
  ⋃ : loans loans -> loans ;; \union : set union of two loan sets.
  [(⋃ loans ()) loans]
  [(⋃ ((ω_1 p_1) ...) ((ω p) (ω_rest p_rest) ...))
   (⋃ ((ω_1 p_1) ... (ω p)) ((ω_rest p_rest) ...))
   (side-condition (not (member (term (ω p)) (term ((ω_1 p_1) ...)))))]
  [(⋃ loans ((ω p) (ω_rest p_rest) ...))
   (⋃ loans ((ω_rest p_rest) ...))]
  )

;; Test for ⋃
(test-equal
 (term (⋃ ((unique x)) ((unique x))))
 (term ((unique x)))
 )
(test-equal
 (term (⋃ ((unique x)) ((unique x) (shared y))))
 (term ((unique x) (shared y)))
 )


(define-metafunction Simple+Γ
  ⋓ : Γr Γr -> Γr ;; \Cup : union the loan sets of then and else.
  [(⋓ Γr_1 ()) Γr_1]
  [(⋓ () Γr_2) Γr_2]
  [(⋓ ((r ↦ loans_1)
       (r_rest1 ↦ loans_rest1) ...) ;; we will iterate over the first environment.
      ((r_before2 ↦ loans_before2)
       ...
       (r ↦ loans_2)
       (r_rest2 ↦ loans_rest2) ...))
   (insert-rgn r (⋃ loans_1 loans_2)
               (⋓ ((r_rest1 ↦ loans_rest1) ...)
                  ((r_before2 ↦ loans_before2) ... (r_rest2 ↦ loans_rest2) ...)))]
  )

;; Tests for ⋓
(test-equal
 (term (⋓ [(r1 ↦ {(unique x)})] [(r1 ↦ {(unique y)})]))
 (term [(r1 ↦ {(unique x) (unique y)})])
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
