#lang racket

;; Require the non-gui version of redex.
(require redex/reduction-semantics)


;; From Figure 1. Term Syntax of Oxide
;; We had to take some liberties with how we represent some
;; of the terms here, because redex requires parens
(define-language Oxide
  ;; Places
  ;;    𝜋 ::= 𝑥.𝑞
  ;; A path from a particular variable to a particular part
  ;; of the object stored there, wheterh taht be a projection
  ;; of a tuple, or a field of a struct.
  ;;
  ;; Places like π are a subset of place expressions that do
  ;; not include dereferences
  (π ::= (pi x n ...))

  ;; Place Exprs.
  ;;    𝑝 ::= 𝑥 | ∗ 𝑝 | 𝑝.𝑛
  (p ::= x  (* p) (dot p n))

  ;; Place Expr. Contexts
  ;;    𝑝□ ::= □ | ∗ 𝑝□ | 𝑝□.𝑛
  ;; These are used in certain parts of the formalism to decompose
  ;; place expressions p into innermost dereferenced place, *π and
  ;; outer context p□.
  (p□ ::= □ (* p□) (dot p□ n))


  ;; Regions
  ;;    ρ ::= ϱ | r
  (ρ ::= ϱ r)

  ;; Constants
  (c ::= () n true false)


  ;; Ownership qualifiers
  ;;    𝜔 ::= shrd | uniq
  (ω ::= shrd uniq)


  ;; Expressions
  (e ::=
     c
     p
     (& r ω p)                ; &r ω p
     (& r ω p[e])             ; &r ω p[e]
     (& r ω p[e e])           ; &r ω p[e1..e2]
     (do e e ...)             ; e1; e2
     (set p e)                ; p := e
     (tup e ...)              ; (e1, ..., en)
     (arr e ...)              ; [e1, ..., en]
     (letrgn [r] e)           ; letrng<r> { e }
     ;; We spell `let` as `define` to be more lispy
     ;;  (let in lisp has certain meaning, and editors (parinfer)
     ;;   dont like it when you use it wrong)
     (define x τ e)           ; let x : τ^si = e1

     ; Scoping: lambdas only have one arg
     (λ τ (x τ) e)            ; |x: τ| → τ_r { e }
     ; TODO: 𝑒𝑓 ::<Φ , 𝜌 , 𝜏si> (𝑒1 , . . . , 𝑒𝑛)
     (if e e e)               ; if e1 { e2 } else { e3 }
     (sub p e)                ; p[e]
     (abort! string)          ; abort!(str)
     (for [x in e] e)         ; for x in e1 { e2 }
     (while e e)              ; while e1 { e2 }

     (Left  [τ τ] e)          ; Left::<τ1, τ2>(e)
     (Right [τ τ] e)          ; Right::<τ1, τ2>(e)
     (match e
            (Left x e)
            (Right x e)))      ; match e { Left(x) ⇒ e, Right(x) ⇒ e }

  ;; Regions: 'x, 'y. Except in this we just use the
  ;; syntactic location instead of requiring a tick
  (r ::= variable-not-otherwise-mentioned)

  ;; A shorter way to spell number
  (n ::= number)

  ;; Variables
  (x ::= variable-not-otherwise-mentioned))


(term
 (letrgn [x]
    (do (let x (Point 1 2))
        (let z (& x shrd x)))))

