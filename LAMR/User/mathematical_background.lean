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
## Exercises

1. 
-/
