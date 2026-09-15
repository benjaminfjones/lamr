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

## 2.5

1. Theorem: sum_{i < n} ar^i = a(r^n-1)/(r-1)
   Proof: n=0 -> 0 = a*(1-1)/(r-1) = 0
          n+1 -> sum_{i<n+1} ar^i = sum_{i<n} ar^i + ar^n = a(r^n-1)/(r-1) + ar^n by induction
              -> _ = a((r^n-1)+(r^n)(r-1))/(r-1) = a(r^n-1+r^(n+1)-r^n)/(r-1) = a(r^(n+1)-1)(r-1)
              -> QED

2. Theorem: n > 4, then n! > 2^n.
   Proof: Recall that (n+1)! = sum_{i=0}^n i*i! + 1
          For n=5, result is clear: 5! = 120 > 32
          Want to show that (n+1)! > 2^(n+1).
          So _ = sum_{i=0}^n i*i! + 1
             _ > low terms + sum_{i=5}^n i*(2^i) + 1
             _ > low terms + sum_{i=5}^n 2*2^i + 1
             _ > sum_{i=5}^n 2^(i+1) >= 2^(n+1) <-- last term since when n > 5

3. Theorem: sum_{i=1}^n 1/(n*(n+1)) = n/(n+1)
   Proof: n=0: 1/1 = 1/1
          n+1: sum_{i=1}^n 1/(n*(n+1)) + 1/((n+1)*(n+2)) =
               n/(n+1) + 1/((n+1)*(n+2)) = (n(n+2) + 1)/((n+1)(n+2))
                                       _ = (n^2 + 2n + 1)/((n+1)(n+2))
                                       _ = (n+1)^2/((n+1)(n+2))
                                       _ = (n+1)/(n+2)
                                       QED

4. Hanoi: for or every n, it takes at least 2^n - 1 moves to move all the disks
   from one peg to another

   Ideas? n=1: 1 peg from A to B can be done in 1 move. 1 move must be taken at least and 2^n - 1
   = 1.
          n+1: Suppose we can move n+1 disks in fewer than 2^(n+1) - 1 moves... ?

          For n=2, 2^n-1 = 3
            if you can do it in 2 moves, then it's one move per disk which is impossible since you
            can't get the larger disk out from under the smaller one w/o the auxiliary move.

          In general, label the disks from smallest D_0 to largest D_{n-1}.
          During solving, D_{n-1} must at some point be moved to peg B. This is
          only possible if D_{n-2} ... D_0 are placed on aux peg C. Then they
          need to be moved onto peg B as well. Let M(n) be the minimal number
          of moves required to move n disks from one peg to another with an
          axiliary. Thus the min number of moves required in the original case
          is M(n) = 2M(n-1) + 1. The recurrance relation has solution 2^n - 1:
          2*(2^(n-1) - 1) + 1 = 2^n - 2 + 1 = 2^n - 1. QED

5. Adjacent peg hanoi:

.
o              .
O          O   o
| | |  ->  | | |  in 8 moves

To move top 2 disks to peg 3 takes 8 moves: move to peg 2 with 4 moves, then flower 2 moves, then move top peg1 2 to the right.
To move a stack of 2 pegs one peg adjacent takes 4 moves and 2 pegs!
To move all 3 disks to peg 3 takes: M(3) = M(2)+1+M(2)+1+M(2) = 3*M(2)+2
  - move top 2 to peg 3   -> 8
  - move big peg to peg 2 -> 1
  - move top 2 to peg 1   -> 8
  - move big peg to peg 3 -> 1
  - move top 2 to peg 3   -> 8
  - total: M(3) = 3*8 + 2
  - note: 8 was M(2)

Conjecture: M(n) = 3*M(n-1) + 2 and that M(n) = 3^n - 1
M(n+1) = 3*M(n) + 2 --> sanity check: 3^(n+1) - 1 = 3*(3^n - 1) + 2 yep!

Use a telecoping series to find M(n) in closed form.

M(n+1) = 3*M(n) + 2
M(n+1) - 3*M(n) = 2
M(n+1)/3 - M(n) = 2/3
define A(n) := M(n)/3^n, so that A(n+1) - A(n) = M(n+1)/3^(n+1) - M(n)/3^n
                                               = M(n+1)/3^(n+1) - 3M(n)/3^(n+1)
                                               = 1/3^(n+1) [ M(n+1) - 3M(n) ]
                                               = 2/3^(n+1)

Now sum from k=0 to n-1:

A(1) - A(0) + A(2) - A(1) + ... + A(n) - A(n-1) = sum_{k=0}_{n-1} 2/3^(k+1)
xxx           xxx    xxx                 xxxxxx
-A(0) + A(n) = 2 sum 1/3^(k+1)
-M(0)/1 + M(n)/3^n = 2 sum 1/3^(k+1)
M(n) = 2 3^n sum 1/3^(k+1)
     = 2 sum_{k=0}^{n-1} 3^n / 3^(k+1)
     = 2 [ 3^(n-1) + 3^(n-2) + ... + 1 ]
     = 2 (1-3^n)/(1-3)  <- exponential sum formula
     = 3^n - 1

QED

6. skipped

7. skipped

8. (2) F_i = F_{i-1} + F_{i-2}
so sum_{i < n} F_i = F_0 + F_1 + F_2 + ... + F_{n-1}
by induction?
n=1: F_0 = F_1 - 1
       0 = 0 check

assume sum_{i < n} F_i = F_{n+1} - 1
then   sum_{i < n+1} F_i = F_{n+1} - 1 + F_n = F_{n+2} - 1 check

8. (3) sum_{i <= n} F_i^2 = F_n F_{n+1}
n=0: F_0^2 = F_0 F_1
       0^2 = 0 * 1 check
assume sum_{i <= n} F_i^2 = F_n F_{n+1}, then

sum_{i <= n+1} F_i^2 = F_n F_{n+1} + F_{n+1}^2 = (F_n + F_{n+1}) F_{n+1}
                                               = F_{n+2} F_{n+1} check

9. skipped
-/
