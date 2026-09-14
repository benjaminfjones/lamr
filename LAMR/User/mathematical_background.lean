/-

```md
# Mathematical Background

## 2.1

### Hanoi

To move n disks from peg A to peg B with auxiliary peg C:
    if n = 0
        return
    else
        move (n-1) disks from peg A to peg C using peg B
        move 1 disk from peg A to peg B (using no aux peg)
        move (n-1) disks from peg C to peg B using aux peg A

input: a b c (numbers of pegs stacked in valid order on pegs A, B, C)
output: List (Nat \times Nat \times Nat) trace of moves
```

-/

partial def hanoi (numDisks start finish aux : Nat) (state : List (Array Nat)) : IO (List (Array Nat)) :=
  match numDisks with
  | 0 => pure state
  | n + 1 => do
    let st' ← hanoi n start aux finish state
    IO.println s!"move 1 disk from peg {start} to peg {finish}"
    let hd := st'[0]!
    let newHead := (hd.set! start (hd[start]!-1)).set! finish (hd[finish]!+1)
    hanoi n aux finish start (newHead :: st')


#eval hanoi 3 0 1 2 [#[3, 0, 0]]

/-

## 2.2

Theorem: For any n >= 3, the sum of the angles in any n-gon is 180(n-2)

Proof: Sum of angles in the triangle is 180 ("Triangle Postulate" - base case).
  Now, take an n-gon and two adjacent sides. Carve off a triangle with those two
  sides and a third. The interior angles of the triangle + those of the (n-1)-gon
  add up to 180((n-1)-2) + 180 by induction. Thus 180(n-2) overall.

--> Required Mathlib

/-- The two geometric inputs of the textbook argument, as hypotheses on a
  purported angle-sum function `S`. -/
  structure AngleSumData (S : ℕ → ℝ) : Prop where
    /-- Triangle Postulate. -/
    base : S 3 = 180
    /-- Two-ears theorem + additivity of interior angles across the diagonal. -/
    step : ∀ n, 4 ≤ n → S n = S (n - 1) + 180

  theorem angleSum_eq {S : ℕ → ℝ} (h : AngleSumData S) :
      ∀ n, 3 ≤ n → S n = 180 * ((n : ℝ) - 2) := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge m 3 with hm | hm
      · have hm2 : m = 2 := by omega
        subst hm2
        norm_num [h.base]
      · have hstep : S (m + 1) = S m + 180 := by
          simpa using h.step (m + 1) (by omega)
        rw [hstep, ih (by omega)]
        push_cast
        ring

### Course-of-values recursion

Fibonacci:

F_0 = 0
F_1 = 1
F_n = F_{n+1} + F_n

N-choose-K:

          | 1                         if k = 0 or k = n
f(n, k) = {
          | (f(n-1, k) + f(n-1, k-1)  else

f is well-founded because the first argument always decreases

f(n, k) = n-choose-k = n! / k! (n - k)!

            | x                  if y = 0
gcd(x, y) = {
            | gcd(y, mod(x, y))  else

gcd is well-founded because the second argument always decreases

-/
