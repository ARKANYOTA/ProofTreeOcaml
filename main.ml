let printf = Printf.printf;;
let sprintf = Printf.sprintf;;
let rev = List.rev;;
type var = char;;

type greek =
| Phi
| Gamma;;
let string_of_greek (g:greek) =
	match g with
	| Phi -> "phi"
	| Gamma -> "gamma";;
let tex_of_greek (g:greek) =
	match g with
	| Phi -> "\\Phi"
	| Gamma -> "\\Gamma";;

type form =
| Var of var
| VarGreek of (greek * int)
| And of form * form
| Impl of form * form
| Or of form * form
| Not of form
| ForAll of var * form
| Exist of var * form
| Vide
| False;;

type seq = form list * form
type rules =
| C_I
| C_EG
| C_ED
| D_IG
| D_ID
| D_E
| I_E
| I_I
| N_I
| N_E
| ABS
| Aff
| V
| Info of rules * (form list);;

let rec tex_string_form (form:form) =
	match form with
	| Var(c) -> sprintf "%c" c
	| VarGreek(g, i) -> sprintf "%s_{%d}" (tex_of_greek g) i
	| And(f1,f2) -> sprintf "(%s \\wedge %s)" (tex_string_form f1) (tex_string_form f2)
	| Impl(f1,f2) -> sprintf "(%s \\rightarrow %s)" (tex_string_form f1) (tex_string_form f2)
	| Or(f1,f2) -> sprintf "(%s \\vee %s)" (tex_string_form f1) (tex_string_form f2)
	| Not(f) -> sprintf "\\neg %s" (tex_string_form f)
	| ForAll(v,f) -> sprintf "\\forall %c.%s" v (tex_string_form f)
	| Exist(v,f) -> sprintf "\\exists %c.%s" v (tex_string_form f)
	| Vide -> sprintf ""
	| False -> sprintf "\\bot";;
let tex_string_seq (seq:seq) =
	let l, f = seq in
	let rec tex_string_liste_form (l:form list) =
		 match l with
		 | [] -> sprintf ""
		 | [f] -> tex_string_form f
		 | f::l -> sprintf "%s, %s" (tex_string_liste_form l) (tex_string_form f)
	in
	sprintf "%s \\vdash %s" (tex_string_liste_form l) (tex_string_form f);;

let rec tex_of_rule (r:rules) =
match r with
| C_I -> "\\wedge_i"
| C_EG -> "\\wedge_{e}^{g}"
| C_ED -> "\\wedge_{e}^{d}"
| D_IG -> "\\vee_{i}^{g}"
| D_ID -> "\\vee_{i}^{d}"
| D_E -> "\\vee_e"
| I_E -> "\\rightarrow_e"
| I_I -> "\\rightarrow_i"
| N_I -> "\\neg_i"
| N_E -> "\\neg_e"
| ABS -> "\\bot"
| Aff -> "\\text{aff}"
| V -> " "
| Info(r, l) -> sprintf "%s \\textcolor{gray}{%s}" (tex_of_rule r) (String.concat " " (List.mapi (fun i x -> sprintf "%s{%s}" (if i=0 then "\\;" else ",") (tex_string_form x)) l));;

type arbre =
| Feuille of seq
| Noeud of seq * arbre list * rules
| FeuilleRef of string;;

let rec affiche_form (form:form) =
	(*with printf*)
	match form with
	| Var(c) -> printf "%c" c
	| VarGreek(g, i) -> printf "%s_%d" (string_of_greek g) i
	| And(f1,f2) -> printf "("; affiche_form f1; printf " /\\ "; affiche_form f2; printf ")"
	| Impl(f1,f2) -> printf "("; affiche_form f1; printf " -> "; affiche_form f2; printf ")"
	| Or(f1,f2) -> printf "("; affiche_form f1; printf " \\/ "; affiche_form f2; printf ")"
	| Not(f) -> printf "¬"; affiche_form f
	| ForAll(v,f) -> printf "∀%c." v; affiche_form f
	| Exist(v,f) -> printf "∃%c." v; affiche_form f
	| Vide -> printf ""
	| False -> printf "⊥";;
let affiche_seq (seq:seq) =
	(*with printf*)
	let l, f = seq in
	let rec affiche_liste_form (l:form list) =
		 match l with
		 | [] -> printf ""
		 | [f] -> affiche_form f
		 | f::l -> affiche_liste_form l ;printf ", "; affiche_form f
	in
	affiche_liste_form l; printf " |- "; affiche_form f;;
let rec string_form (form: form) =
	(*with sprintf*)
	match form with
	| Var(c) -> sprintf "%c" c
	| VarGreek(g, i) -> sprintf "%s_%d" (string_of_greek g) i
	| And(f1,f2) -> sprintf "(%s /\\ %s)" (string_form f1) (string_form f2)
	| Impl(f1,f2) -> sprintf "(%s -> %s)" (string_form f1) (string_form f2)
	| Or(f1,f2) -> sprintf "(%s \\/ %s)" (string_form f1) (string_form f2)
	| Not(f) -> sprintf "¬%s" (string_form f)
	| ForAll(v,f) -> sprintf "∀%c.%s" v (string_form f)
	| Exist(v,f) -> sprintf "∃%c.%s" v (string_form f)
	| Vide -> sprintf ""
	| False -> sprintf "⊥";;

let string_seq (seq:seq):string =
	(*with sprintf*)
	let l, f = seq in
	let rec string_liste_form (l:form list) =
		 match l with
		 | [] -> sprintf ""
		 | [f] -> string_form f
		 | f::l -> sprintf "%s, %s" (string_liste_form l) (string_form f);
	in
	sprintf "%s |- %s" (string_liste_form l) (string_form f);;

let rec affiche_arbre ?(n=0) (a:arbre) =
	match a with
	| Feuille(seq) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"
	| Noeud(seq, l, _) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"; List.iter (fun x -> affiche_arbre ~n:(n+1) x) l
	| FeuilleRef(s) -> printf "%s" (String.make (n*4) ' '); printf "%s\n" s;;
let arbre_to_tex (a:arbre) =
	let list = ref [] in
	let rec aux (a:arbre) =
		match a with
		| Feuille(seq) -> list := (sprintf "  \\AxiomC{} \\RightLabel{$\\text{ax}$} \\UnaryInfC{$%s$}\n" (tex_string_seq seq))::!list
		| Noeud(seq, l, r) ->
			(match List.length l with
			| 0 -> failwith "arbre_to_tex : no son"
			| 1 -> list := (sprintf "  \\UnaryInfC{$%s$}\n" (tex_string_seq seq))::!list
			| 2 -> list := (sprintf "  \\BinaryInfC{$%s$}\n" (tex_string_seq seq))::!list
			| 3 -> list := (sprintf "  \\TrinaryInfC{$%s$}\n" (tex_string_seq seq))::!list
			| _ -> failwith "arbre_to_tex : too many sons");

			list := (sprintf "  \\RightLabel{$%s$}\n" (tex_of_rule r))::(!list);
			List.iter (fun x -> aux x) (List.rev l);
		| FeuilleRef(s) -> list := (sprintf "  \\AxiomC{$(\\text{%s})$}\n" s)::!list

	in
	aux a;

	let s = ref "\\begin{prooftree}\n" in
	List.iter (fun x -> s := !s ^ x) !list;
	!s^"\n\\end{prooftree}";;

let c_i (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| And(phi1,phi2) -> (gamma, phi1), (gamma, phi2)
	| _ -> failwith "c_i : phi is not a conjunction";;
let c_eg (seq: seq) (phi2: form) =
	let gamma, phi1 = seq in
	(gamma, And(phi1,phi2));;
let c_ed (seq: seq) (phi1: form) =
	let gamma, phi2 = seq in
	(gamma, And(phi1,phi2));;
let d_ig (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| Or(phi1,phi2) -> (gamma, phi1)
	| _ -> failwith "d_ig : phi is not a disjunction";;
let d_id (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| Or(phi1,phi2) -> (gamma, phi2)
	| _ -> failwith "d_id : phi is not a disjunction";;
let d_e (seq: seq) (phi1: form) (phi2: form) =
	let gamma, phi = seq in
	(gamma, Or(phi1,phi2)), (phi1::gamma, phi), (phi2::gamma, phi);;
let i_e (seq: seq) (phi1: form) =
	let gamma, phi2 = seq in
	(gamma, Impl(phi1,phi2)), (gamma, phi1)
let i_i (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| Impl(phi1,phi2) -> (phi1::gamma, phi2)
	| _ -> failwith "i_i : phi is not an implication";;
let n_i (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| Not(newphi) -> (newphi::gamma, False)
	| _ -> failwith "n_i : phi is not a negation";;
let n_e (seq: seq) (phi: form) =
	let gamma, faux = seq in
	match faux with
	| False -> (gamma, Not(phi)), (gamma, phi)
	| _ -> failwith "n_e : faux is not a negation";;
let abs (seq: seq) =
	let gamma, phi = seq in
	(Not(phi)::gamma, False);;
let aff (seq: seq) (l:int list) =
    (seq);;

let rec ax (seq: seq):bool =
	let gamma, phi = seq in
	match gamma with
	| [] -> false
	| f::l when f = phi -> true
	| f::l -> ax (l, phi);;

let rec axs (seql: seq list): bool =
	match seql with
	| [] -> false
	| seq::l when ax seq -> true
	| seq::l -> axs l;;





let p = Var('p');;
let q = Var('q');;
let r = Var('r');;


let print_section (title: string) =
	printf "\n\\section{%s}\n" title;;
let print_subsection (title: string) =
	printf "\n\\subsection{%s}\n" title;;


printf "%s" (
"\\input{packages.tex}"^
"\n\\begin{document}"^
"\n\\tableofcontents"
);;

print_section "Sylogismes";;
print_subsection "Modus Ponens";;
let arbre_modus_ponens =
	let modus_ponens = rev [Impl(p, q); p], q in
	let a, b = i_e modus_ponens p in
	Noeud(modus_ponens, [
		Feuille(a);
		Feuille(b)
	], Info(I_E, [p]));;
printf "%s" (arbre_to_tex arbre_modus_ponens);;

print_subsection "Modus Tollens";;
let arbre_modus_tollens =
	let modus_tollens = rev [Impl(p, q); Not(q)], Not(p) in
	let a = n_i modus_tollens in
	let b,c = n_e a q in
	Noeud(modus_tollens,[
		Noeud(a, [
			Noeud(c, [
				FeuilleRef("Modus Ponens")]
			, V);
			Feuille(b)
		], Info(N_E, [q]))
	], N_I);;
printf "%s" (arbre_to_tex arbre_modus_tollens);;

print_subsection "Syllogisme disjonctif";;
let arbre_syllogisme_disjonctif =
	let syllogisme_disjonctif = rev [Or(p, q); Not(p)], q in
	let a,b,c = d_e syllogisme_disjonctif p q in
	let b1 = abs b in
	let b11, b12 = n_e b1 p in

	Noeud(syllogisme_disjonctif, [
		Feuille(a);
		Noeud(b, [
			Noeud(b1, [
				Feuille(b11);
				Feuille(b12)
			], Info(N_E, [p]))
		], ABS);
		Feuille(c)
	], Info(D_E, [p;q]));;
printf "%s" (arbre_to_tex arbre_syllogisme_disjonctif);;

print_subsection "Syllogisme barbara";;
let arbre_syllogisme_barbara =
	let syllogisme_barbara = rev [Impl(p, q); Impl(q, r)], Impl(p, r) in
	let a = i_i syllogisme_barbara in
	let b,c = i_e a q in
	Noeud(syllogisme_barbara, [
		Noeud(a, [
			Feuille(b);
			Noeud(c, [
				FeuilleRef("Modus Ponens")
			], V)
		], Info(I_E,[q]))
	], I_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_barbara);;

print_subsection "Syllogisme Festino";;
let arbre_syllogisme_festino =
	let syllogisme_festino = rev [Impl(p, Not(q)); q], Not(p) in
	let a = n_i syllogisme_festino in
	let b,c = n_e a q in
	Noeud(syllogisme_festino, [
		Noeud(a, [
			Noeud(b, [
				 FeuilleRef("Modus Ponens")
			], V);
			Feuille(c)
		], Info(N_E, [q]))
	], N_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_festino);;

print_subsection "Syllogisme Cesare";;
let arbre_syllogisme_cesare =
	let syllogisme_cesare = rev [Impl(p, Not(q)); Impl(r, q)], Impl(r, Not(p)) in
	let a = i_i syllogisme_cesare in
	let b = n_i a in
	let c,d = n_e b q in

	Noeud(syllogisme_cesare, [
		Noeud(a, [
			Noeud(b, [
				 Noeud(c, [
				   FeuilleRef("Modus Ponens")
				 ], V);
				Noeud(d, [
					FeuilleRef("Modus Ponens")
				], V)
			], Info(N_E, [q]));
		], N_I)
	], I_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_cesare);;



printf "\n\\end{document}"