module Interface
open System.Text.RegularExpressions
open System.IO

let (|Reg|_|) regex str =
   let m = Regex(regex, RegexOptions.IgnoreCase).Match(str)
   if m.Success
   then Some [ for x in m.Groups -> x.Value ].Tail
   else None

let parseUnary (s: string) x =
    match s with
    | Reg @"not|[~￢-]" []
        -> Logic.Imp(x, Logic.Contra)
    | _ -> raise (System.ArgumentException("Parsing Error: " + s))
let parseBinary (s: string) x y =
    match s with
    | Reg @"and|/\\|[∧∩*]" []
        -> Logic.And(x, y)
    | Reg @"or|\\/|[∨∪+]" []
        -> Logic.Or(x, y)
    | Reg @"imp|[-=]>|[→⇒⊃]" []
        -> Logic.Imp(x, y)
    | _ -> raise (System.ArgumentException("Parsing Error: " + s))
let rec parse (s: string) =
    match s.Replace(" ", "") with
    | "⊥" | "×"
        -> Logic.Contra
    | Reg @"^\(([^\(\)]*(?:(?:(?'Open'\()[^\(\)]*)+(?:(?'Close-Open'\))[^\(\)]*)+)*(?(Open)(?!)))\)$" (x :: _)
        -> parse x
    | Reg @"^((?:(?:(?'Open'\()[^\(\)]*)+(?:(?'Close-Open'\))[^\(\)]*)+)*(?(Open)(?!)|(?<=\)))|[A-Z⊥×])(and|or|imp|/\\|\\/|[-=]>|[∧∩*∨∪+→⇒⊃])((?:(?:(?'Open'\()[^\(\)]*)+(?:(?'Close-Open'\))[^\(\)]*)+)*(?(Open)(?!)|(?<=\)))|[A-Z⊥×])$" (x :: o :: y :: _)
        -> parseBinary o (parse x) (parse y)
    | Reg @"^(not|[~￢-])((?:(?:(?'Open'\()[^\(\)]*)+(?:(?'Close-Open'\))[^\(\)]*)+)*(?(Open)(?!)|(?<=\)))|[A-Z⊥×])$" (o :: x :: _)
        -> parseUnary o (parse x)
    | Reg @"^([A-Z])$" [x]
        -> Logic.Prop(x)
    | _ -> raise (System.ArgumentException("Parsing Error: " + s))


let interpreter argv =
    match argv with
    | [| "-o"; l; x |]
        -> let f = parse x
           let p = Logic.prove f
           Logic.makedoc l p
           printfn "Successfuly Written: %s" l
    | [| "-s"; x |]
        -> let f = parse x
           Logic.test <- true
           ignore <| Logic.prove f
    | [|x|]
        -> let f = parse x
           printfn "Prove %s" (Logic.tostrFormula f)
           let mutable i = 0
           for p in Logic.prove f do
               i <- i+1
               printfn ""
               printfn " Proof No. %d" i
               Logic.showProof p
           if i = 0
           then printfn " No Proof Found."
                if Logic.exam f
                then printfn " However my tableau says it is provable..."
    | _B
        -> printfn "
      - PureProof -

 Developed by @2_7182818
 Please tell me when you find a tautology which can't be proved!


>pp [-o FILENAME] [-s] \"FORMULA\"

-o FILENAME  : Output a TeX file. You need proof.sty to complile it.
-s           : Show all steps.

Formula Example: ((P or (not Q)) and Q) imp P
"


[<EntryPoint>]
let main argv =
    try
        interpreter argv
    with
        | ex -> eprintfn "Error: %s" ex.Message
    0
(*  TEST CODE
    let a = Logic.Prop("A")
    let b = Logic.Prop("B")
    let c = Logic.Prop("C")
    let d = Logic.Prop("D")
    let wff = [
        (a + b) <=> (b + a)   // 2-1
        ; (a * b) <=> (b * a)   // 2-2
        ; a + b * c <=> (a + b) * (a + c)       // 2-3
        ; a * (b + c) <=> (a * b) + (a * c)     // 2-4
        ; a * b * c => (a * b) + (c * d)        // 2-5
        ; a * a <=> a           // 2-6
        ; a * b => a + b        // 2-7
        ; (a => (b => c)) <=> (b => (a => c))   // 3-1
        ; (a => b) * (b => c) => (a => c)       // 3-2
        ; (a => (b => c)) <=> (a * b => c)      // 3-3
        ; (a => (b * c)) <=> ((a => b) * (a => c))   // 3-4
        ; ((a => b) + (a => c)) => (a => (b + c))   // 3-5
        ; ((a + b) => c) <=> ((a => c) * (b => c))   // 3-6
        ; (a => (b => c)) => ((a => b) => (a => c)) // 3-7
        ; ((a => c) + (b => c)) => ((a * b) => c)   // 3-8  conv:classic
        ; a => -(-a)            // 4-1
        ; (a => b) => (-b => -a)  // 4-2
        ; -(a + b) => -a * -b   // 4-3
        ; -(a * b) => -a + -b   // 4-4 classic
        ; a + -a                // 4-5 classic
        ; (a + b) * -b => a     // 4-6 intuition
        ; a => (-a => b)        // 4-7 intuition
        
        // http://www.math.h.kyoto-u.ac.jp/~takasaki/edu/logic/logic7.html
        ; a => a
        ; a * -a => b
        ; (a => b) * (b => c) => (a => c)
        ; a => -(-a)
        ; -(-a) => a            // classic
        ; a => (b => a)
        ; (a => (b => c)) => ((a => b) => (a => c))
        ; (-b => -a) => (a => b)    // classic

        // ISbN4-326-10158-X
        ; a * b => b * a
        ; b * a => a * b
        ; a * (b * c) => (a * b) * c
        ; (a * b) * c => a * (b * c)
        ; a * a => a
        ; a => a * a
        ; a + b => b + a
        ; b + a => a + b
        ; a + (b + c) => (a + b) + c
        ; (a + b) + c => a + (b + c)
        ; a + a => a
        ; a => a + a
        ; (a * b) + (a * c) => a * (b + c)
        ; a * (b + c) => (a * b) + (a * c)
        ; a + (b * c) => (a + b) * (a + c)
        ; (a + b) * (a + c) => a + (b * c)
        ; a * (a + b) => a
        ; a => a * (a + b)
        ; a + (a * b) => a
        ; a => a + (a * b)

        ; (a => b) * (a => c) => (a => (b * c))
        ; (a => b) * (b => c) => (a => c)
        ; (a => c) * (b => c) * (a + b) => c

        ; ((a => b) => c) => (((b => a) => c) => c)
        ]
    for p in wff do
        printfn "%s : %b" (Logic.tostrFormula p) (Logic.exam p)
        //let q = prove p
        //if q.Length = 0 then printfn "%s : %d proofs" (tostrFormula p) (q.Length)
    //let x = (-(a * b) => -a + -b)
    //printfn "%s" (prove x |> List.head |> (fun x -> toLaTeX x "" "    "))
    ignore <| stdin.ReadLine()
    0
*)
