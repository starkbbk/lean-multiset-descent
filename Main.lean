import Descent.Executor
import Descent.Battle
import Descent.Goodstein

open Descent

/-- Enumerate every list of the requested length over ranks 0,1,2,3. -/
def worklists : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range 4).flatMap fun rank => (worklists n).map (rank :: ·)

/-- Independent bounded FIFO simulation, unlike the verified depth-first executor.
Fuel belongs only to this regression oracle, never to the verified normalizer. -/
def referenceRun (children : Nat) : Nat → List Nat → Option Nat
  | 0, [] => some 0
  | 0, _ :: _ => none
  | _ + 1, [] => some 0
  | fuel + 1, 0 :: rest => (referenceRun children fuel rest).map (· + 1)
  | fuel + 1, (rank + 1) :: rest =>
      (referenceRun children fuel (rest ++ List.replicate children rank)).map (· + 1)

/-- A path of the given number of edges from the root to its only head. -/
def path : Nat → Hydra
  | 0 => .node []
  | n + 1 => .node [path n]

/-- Small hydras whose Kirby–Paris battles finish quickly. The four-edge path does not. -/
def hydraSamples : List Hydra :=
  let h : Hydra := .node []
  [path 1, path 2, path 3, .node [h, h, h, h, h], .node [.node [h, h]],
    .node [.node [h], .node [h]], .node [h, .node [h, h]], .node [h, h, .node [h, h]],
    .node [.node [h], .node [h, h]], .node [.node [h], .node [h, h], h]]

def isDead : Hydra → Bool
  | .node [] => true
  | _ => false

def main : IO UInt32 := do
  IO.println "MULTISET DESCENT | termination with sharp complexity certificates"
  IO.println "Examples: binary branching, single task, ranks 0 through 8"
  for rank in List.range 9 do
    let actual := Executor.steps (fun _ => 2) [rank]
    IO.println s!"rank={rank}: transitions={actual}, closed form={2 ^ (rank + 1) - 1}"
  IO.println "A legal expansion [2] -> [1,1,1] increases length 1->3 and rank sum 2->3."
  IO.println "All such schedules terminate, even when these simpler measures grow."
  let mut configurations := 0
  for children in List.range 4 do
    for length in List.range 4 do
      for tasks in worklists length do
        let policy := fun _ => children
        let actual := Executor.steps policy tasks
        let predicted := potential policy (tasks : Multiset Nat)
        let oracle := referenceRun children 1000 tasks
        if actual != predicted || oracle != some predicted ||
            Executor.steps policy tasks.reverse != actual || Executor.finish policy tasks != [] then
          IO.eprintln s!"FAIL: children={children}, tasks={tasks}, steps={actual}, budget={predicted}, FIFO={oracle}"
          return 1
        configurations := configurations + 1
  IO.println s!"PASS: {configurations} configurations; verified executor, independent FIFO simulator, reversed order, and normal form agree."
  IO.println "HYDRA BATTLES | Kirby–Paris schedule: stage n regrows n new copies"
  let mut battles := 0
  for hydra in hydraSamples do
    let moves := Hydra.kirbyParisLength hydra
    let (final, stage) := Hydra.finalState id hydra
    if !isDead final || stage != moves + 1 then
      IO.eprintln s!"FAIL: hydra={hydra.render}, counter={moves}, normalizer stage={stage}"
      return 1
    IO.println s!"KP hydra={hydra.render} moves={moves}"
    battles := battles + 1
  IO.println s!"PASS: {battles} battles; move counter and generic normalizer agree, and every hydra dies."
  IO.println "GOODSTEIN | stage k writes the value in hereditary base k+2, rewrites it in base k+3, subtracts one"
  for n in List.range 4 do
    let length := Goodstein.goodsteinLength n
    if Goodstein.goodstein n length != 0 ||
        (List.range length).any (fun k => Goodstein.goodstein n k == 0) ||
        (List.range 3).any (fun j => Goodstein.goodstein n (length + j + 1) != 0) then
      IO.eprintln s!"FAIL: goodstein n={n} length={length}"
      return 1
    IO.println s!"GOODSTEIN n={n} length={length}"
  for n in [4, 5] do
    let values := (List.range 10).map (Goodstein.goodstein n)
    IO.println s!"GOODSTEIN n={n} prefix={",".intercalate (values.map toString)}"
  IO.println "PASS: Goodstein lengths come from a total search justified by goodstein_terminates."
  IO.println "Finite regression checks supplement the universal kernel-checked theorems."
  return 0
