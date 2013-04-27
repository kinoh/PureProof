module Logic

// Basic Definitions

type Formula =
    | Contra
    | Prop of string
    | Imp of Formula * Formula
    | And of Formula * Formula
    | Or of Formula * Formula
    static member (=>) (p: Formula, q: Formula) = Imp(p, q)
    static member (*) (p: Formula, q: Formula) = And(p, q)
    static member (+) (p: Formula, q: Formula) = Or(p, q)
    static member (~-) (p: Formula) = Imp(p, Contra)
    static member (<=>) (p: Formula, q: Formula) = And(Imp(p, q), Imp(q, p))

type Proof =
    | Base of Formula
    | Assume of Formula
    | Infer of (Proof list) * Formula * string

type Context = Formula * (Proof list)


let conc (p: Proof) =
    match p with
    | Base(a)
    | Assume(a)
        -> a
    | Infer(_, a, _)
        -> a

let fold1 (f: 'State -> 'State -> 'State) (g: 'T -> 'State) (l: 'T list) : 'State =
    List.fold (fun s t -> f s (g t)) (g l.Head) l.Tail
let exceptBy (f: 'T -> 'T -> bool) (a: 'T) (l: 'T list) =
    List.filter (not << (f a)) l


//  Output Formatting

let andI = "∧I"
let orI1 = "∨I1"
let orI2 = "∨I2"
let notI = "￢I"
let impI = "→I"
let andE1 = "∧E1"
let andE2 = "∧E2"
let orE = "∨E"
let notE = "￢E"
let impE = "→E"
let abs = "AB"
let dneg = "DN"

let padRightMulti (s: string) m =
    let n = System.Text.UnicodeEncoding.UTF8.GetByteCount(s) - s.Length
    s.PadRight(m - n/2)


let rec tostrFormula (f: Formula) =
    match f with
    | Contra
        -> "⊥"
    | Prop(p)
        -> p
    | Imp(p, Contra)
        -> sprintf "￢%s" (tostrFormula p)
    | Imp(p, q)
        -> sprintf "(%s → %s)" (tostrFormula p) (tostrFormula q)
    | And(p, q)
        -> sprintf "(%s ∧ %s)" (tostrFormula p) (tostrFormula q)
    | Or(p, q)
        -> sprintf "(%s ∨ %s)" (tostrFormula p) (tostrFormula q)
let rec showProofRec (p: Proof) (n: int ref) =
    match p with
    | Base(x)
        -> printfn "%3d: %s" !n (tostrFormula x)
    | Assume(x)
        -> printfn "%3d: [%s]" !n (tostrFormula x)
    | Infer(x, y, t)
        -> let m = [ for p in (List.rev x) -> (showProofRec p n).ToString() ]
           printfn "%3d: %s (%s %s)"
               !n
               (padRightMulti (tostrFormula y) 40)
               ((String.concat "," m).PadRight(5))
               t
    n := !n + 1
    !n - 1
let showProof p =
    ignore <| showProofRec p (ref 0)

let ntoLaTeX (s: string) =
    s.Replace("∧", "\\land ")
        .Replace("∨", "\\lor ")
        .Replace("￢", "\\lnot ")
        .Replace("→", "\\to ")
        .Replace("1", "_1")
        .Replace("2", "_2")
let rec ftoLaTeX (f: Formula) =
    match f with
    | Contra
        -> "\\bot "
    | Prop(p)
        -> p
    | Imp(p, Contra)
        -> sprintf "\\lnot %s" (ftoLaTeX p)
    | Imp(p, q)
        -> sprintf "(%s \\to %s)" (ftoLaTeX p) (ftoLaTeX q)
    | And(p, q)
        -> sprintf "(%s \\land %s)" (ftoLaTeX p) (ftoLaTeX q)
    | Or(p, q)
        -> sprintf "(%s \\lor %s)" (ftoLaTeX p) (ftoLaTeX q)
let rec toLaTeX (p: Proof) (i: string) (u: string) =
    match p with
    | Base(x)
        -> sprintf "%s%s" i (ftoLaTeX x)
    | Assume(x)
        -> sprintf "%s[%s]" i (ftoLaTeX x)
    | Infer(x, y, t)
        -> sprintf "%s\\infer[(%s)]{ %s }{\r\n%s\r\n%s}"
                i
                (ntoLaTeX t)
                (ftoLaTeX y)
                (fold1 (fun s a -> s + "\r\n" + i + u + "&\r\n" + a) (fun z -> toLaTeX z (i + u) u) x)
                i

let makedoc (file: string) (proofs: Proof list) =
    System.IO.File.WriteAllLines(file,
        ["\\documentclass[]{article}"
        ; "\\usepackage{proof}"
        ; "\\setlength{\\oddsidemargin}{0mm}"
        ; "\\setlength{\\topmargin}{-20mm}"
        ; "\\setlength{\\textwidth}{160mm}"
        ; "\\setlength{\\textheight}{240mm}"
        ; ""
        ; "\\begin{document}" ]
        @ [for p in proofs ->
            "\\[\r\n" + (toLaTeX p "" "  ") + "\r\n\\]\r\n\r\n"
        ] @
        [ "\\end{document}" ])


// Log

let mutable test = false
let mutable dedlev = 0
let mutable indent = ""
let indunit = "  "

let logmsg s f p = if test then printfn "%s%s%s %s %A" (if dedlev > 0 then "#" else " ") indent s (tostrFormula f) (List.map (conc >> tostrFormula) p)
let log m f = if test then printfn "%s%s%s %s" (if dedlev > 0 then "#" else " ") indent m (tostrFormula f)
let addind () = if test then indent <- indent + indunit
let subind () = if test then indent <- indent.[indunit.Length..]



// Tableaux

let rec examRec (l: Formula list) (t: string list) (f: string list) =
    match l with
    | [] -> false
    | Contra :: _
        -> true
    | Imp(Imp(x, Contra), Contra) :: r
        -> examRec (x :: r) t f
    | Imp(Prop(x), Contra) :: r
        -> if List.exists ((=) x) t
           then true
           else examRec r t (x :: f)
    | Imp(And(x, y), Contra) :: r
        -> examRec (-x :: r) t f && examRec (-y :: r) t f
    | Imp(Or(x, y), Contra) :: r
        -> examRec (-x :: -y :: r) t f
    | Imp(Imp(x, y), Contra) :: r
        -> examRec (x :: -y :: r) t f
    | Prop(x) :: r
        -> if List.exists ((=) x) f
           then true
           else examRec r (x :: t) f
    | And(x, y) :: r
        -> examRec (x :: y :: r) t f
    | Or(x, y) :: r
        -> examRec (x :: r) t f && examRec (y :: r) t f
    | Imp(x, y) :: r
        -> examRec (-x :: r) t f && examRec (y :: r) t f
let exam (f: Formula) =
    examRec [Imp(f, Contra)] [] []



// Natural Deduction

let concluded (f: Formula) (prems: Proof list) =
    List.exists (fun p -> f = conc p) prems
let why (f: Formula) (prems: Proof list) =
    List.find (fun p -> f = conc p) prems
let compconc (p: Proof) (q: Proof) =
    conc p = conc q
let rec getPrems (p: Proof) =
    match p with
    | Base(_)
    | Assume(_)
        -> []
    | Infer(a, b, _)
        -> a @ List.collect getPrems a

let rec andElim (p: Proof) =
    match conc p with
    | And(a, b)
        -> log "andE" (conc p)
           (fun x -> x @ List.collect andElim x) [ Infer([p], a, andE1); Infer([p], b, andE2) ]
    | _ -> []
let rec impElim (prems: Proof list) (p: Proof) (s: Context list) =
    match conc p with
    | Imp(a, b)
        when not <| concluded b prems
        -> log "impE" (conc p)
           [ for x in proveRec a prems s -> Infer([p; x], b, if b = Contra then notE else impE) ] @ prems
    | _ -> prems
and deduce (prems: Proof list) (s: Context list) =
    dedlev <- dedlev + 1
    let ind = List.collect andElim prems
                |> List.filter (fun x -> not <| concluded (conc x) prems)
    let p = ind @ prems
    let q = (List.fold (fun t p -> impElim t p s)) p p
    if p <> q
    then deduce q s
    else dedlev <- 0
         q

and proveDet (f: Formula) (prems: Proof list) (s: Context list) =
    match f with
    | a
        when concluded a prems
        -> log "proved" f
           [ why a prems ]
    | Imp(a, b)
        -> log "impI" f
           let q = if concluded a prems
                   then prems
                   else Assume(a) :: prems
           [ for p in proveRec b q s -> Infer([p], f, if b = Contra then notI else impI) ]
    | And(a, b)
        -> log "andI" f
           List.concat
             [ for p in proveRec a prems s ->
               [ for q in proveRec b prems s -> Infer([p; q], f, andI) ] ]
    | Or(a, b)
        -> log "orI" f
           [ for p in proveRec a prems s -> Infer([p], f, orI1) ]
             @ [ for p in proveRec b prems s -> Infer([p], f, orI2) ]
    | _ -> []

and orElim (f: Formula) (prems: Proof list) (s: Context list) (p: Proof) =
    match conc p with
    | Or(a, b)
        -> if concluded a prems || concluded b prems
           then []
           else log "orE" f
                let q = exceptBy compconc p prems
                List.concat
                  [ for x in proveRec f (Assume(a) :: q) s ->
                    [ for y in proveRec f (Assume(b) :: q) s -> Infer([p; x; y], f, orE) ] ]
    | _ -> []
and absurd (f: Formula) (p: Proof) =
    match conc p with
    | Contra
        when f <> Contra
        -> log "contradiction!" f
           [ Infer([p], f, abs) ]
    | _ -> []

and proveRec (f: Formula) (prems: Proof list) (s: Context list) =
    logmsg "prove" f prems
    addind ()
    if List.exists ((=) (f, prems)) s
    then log "avoid loop" f
         subind ()
         []
    else let t = (f, prems) :: s
         let ps = deduce prems t
         let p = proveDet f ps t
         let q = List.collect (orElim f ps t) ps
         let r = List.collect (absurd f) ps
         subind ()
         log (([p; q; r] |> List.map List.length |> List.sum).ToString() + " proofs:") f
         p @ q @ r

let prove f =
    let p = proveRec f [] []
    if p.Length = 0
    then proveRec (Imp(Imp(f, Contra), Contra)) [] []
           |> List.map (fun x -> Infer([x], f, dneg))
    else p
