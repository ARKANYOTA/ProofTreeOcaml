let printf = Printf.printf;;
let sprintf = Printf.sprintf;;
type var = char;;

type form =
| Var of var
| And of form * form
| Impl of form * form
| Or of form * form
| Not of form
| ForAll of var * form
| Exist of var * form
| Vide
| False;;

type trueseq = form list * form;;

type seq =
| Seq of trueseq
| Ref of string;;
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
| V;;
let tex_of_rule (r:rules) =
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
| V -> " ";;

type arbre =
| Feuille of seq
| Noeud of seq * arbre list * rules;;

let rec affiche_form (form:form) =
	(*with printf*)
	match form with
	| Var(c) -> printf "%c" c
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
	match seq with
	| Ref(s) -> printf "%s" s
	| Seq(l,f) ->
		let rec affiche_liste_form (l:form list) =
			match l with
			| [] -> printf ""
			| [f] -> affiche_form f
			| f::l -> affiche_form f; printf ", "; affiche_liste_form l;
	in
	affiche_liste_form l; printf " |- "; affiche_form f;;
let rec string_form (form: form) =
	(*with sprintf*)
	match form with
	| Var(c) -> sprintf "%c" c
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
	match seq with
	| Ref(s) -> sprintf "%s" s
	| Seq(l,f) ->
		let rec string_liste_form (l:form list) =
			match l with
			| [] -> sprintf ""
			| [f] -> string_form f
			| f::l -> sprintf "%s, %s" (string_form f) (string_liste_form l);
	in
	sprintf "%s |- %s" (string_liste_form l) (string_form f);;

let rec tex_string_form (form:form) =
	match form with
	| Var(c) -> sprintf "%c" c
	| And(f1,f2) -> sprintf "(%s \\wedge %s)" (tex_string_form f1) (tex_string_form f2)
	| Impl(f1,f2) -> sprintf "(%s \\rightarrow %s)" (tex_string_form f1) (tex_string_form f2)
	| Or(f1,f2) -> sprintf "(%s \\vee %s)" (tex_string_form f1) (tex_string_form f2)
	| Not(f) -> sprintf "\\neg %s" (tex_string_form f)
	| ForAll(v,f) -> sprintf "\\forall %c.%s" v (tex_string_form f)
	| Exist(v,f) -> sprintf "\\exists %c.%s" v (tex_string_form f)
	| Vide -> sprintf ""
	| False -> sprintf "\\bot";;
let tex_string_seq (seq:seq) =
	match seq with
	| Ref(s) -> sprintf "\\text{%s}" s
	| Seq(l,f) ->
		let rec tex_string_liste_form (l:form list) =
			match l with
			| [] -> sprintf ""
			| [f] -> tex_string_form f
			| f::l -> sprintf "%s, %s" (tex_string_form f) (tex_string_liste_form l)
	in
	sprintf "%s \\vdash %s" (tex_string_liste_form l) (tex_string_form f);;
let rec affiche_arbre ?(n=0) (a:arbre) =
	match a with
	| Feuille(seq) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"
	| Noeud(seq, l, _) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"; List.iter (fun x -> affiche_arbre ~n:(n+1) x) l;;
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
	in
	aux a;

	let s = ref "\\begin{prooftree}\n" in
	List.iter (fun x -> s := !s ^ x) !list;
	!s^"\n\\end{prooftree}";;

let c_i (seq: trueseq) =
	let gamma, phi = seq in
	match phi with
	| And(phi1,phi2) -> (gamma, phi1), (gamma, phi2)
	| _ -> failwith "c_i : phi is not a conjunction";;
let c_eg (seq: trueseq) (phi2: form) =
	let gamma, phi1 = seq in
	(gamma, And(phi1,phi2));;
let c_ed (seq: trueseq) (phi1: form) =
	let gamma, phi2 = seq in
	(gamma, And(phi1,phi2));;
let d_ig (seq: trueseq) =
	let gamma, phi = seq in
	match phi with
	| Or(phi1,phi2) -> (gamma, phi1)
	| _ -> failwith "d_ig : phi is not a disjunction";;
let d_id (seq: trueseq) =
	let gamma, phi = seq in
	match phi with
	| Or(phi1,phi2) -> (gamma, phi2)
	| _ -> failwith "d_id : phi is not a disjunction";;
let d_e (seq: trueseq) (phi1: form) (phi2: form) =
	let gamma, phi = seq in
	(gamma, Or(phi1,phi2)), (phi1::gamma, phi), (phi2::gamma, phi);;
let i_e (seq: trueseq) (phi1: form) =
	let gamma, phi2 = seq in
	(gamma, Impl(phi1,phi2)), (gamma, phi1)
let i_i (seq: trueseq) =
	let gamma, phi = seq in
	match phi with
	| Impl(phi1,phi2) -> (phi1::gamma, phi2)
	| _ -> failwith "i_i : phi is not an implication";;
let n_i (seq: trueseq) =
	let gamma, phi = seq in
	match phi with
	| Not(newphi) -> (newphi::gamma, False)
	| _ -> failwith "n_i : phi is not a negation";;
let n_e (seq: trueseq) (phi: form) =
	let gamma, faux = seq in
	match faux with
	| False -> (gamma, Not(phi)), (gamma, phi)
	| _ -> failwith "n_e : faux is not a negation";;
let abs (seq: trueseq) =
	let gamma, phi = seq in
	(Not(phi)::gamma, False);;





let p = Var('p');;
let q = Var('q');;
let r = Var('r');;


let print_section (title: string) =
	printf "\n\\section{%s}\n" title;;
let print_subsection (title: string) =
	printf "\n\\subsection{%s}\n" title;;


printf "%s" (
"\n\\documentclass{article}"^
"\n\\usepackage[left=1.5cm, right=2cm]{geometry}"^
"\n\\usepackage{graphicx}"^
"\n\\usepackage{bussproofs}"^
"\n\\usepackage{amsmath}"^
"\n\\usepackage{color}"^
"\n\\usepackage{hyperref}"^
"\n\\hypersetup{linktocpage}"^
"\n\\begin{document}"^
"\n\\tableofcontents"
);;

print_section "Sylogismes";;
print_subsection "Modus Ponens";;
let arbre_modus_ponens =
	let modus_ponens = [Impl(p, q); p], q in
	let a, b = i_e modus_ponens (p) in
	Noeud(Seq(modus_ponens), [Feuille(Seq(a)); Feuille(Seq(b))], I_E);;
printf "%s" (arbre_to_tex arbre_modus_ponens);;

print_subsection "Modus Tollens";;
let arbre_modus_tollens =
	let modus_tollens = [Impl(p, q); Not(q)], Not(p) in
	let a = n_i modus_tollens in
	let b,c = n_e a q in
	Noeud(Seq(modus_tollens),[
		Noeud(Seq(a), [
			Noeud(Seq(c), [
				Feuille(Ref("Modus Ponens"))]
			, V);
			Feuille(Seq(b))
		], N_E)
	], N_I);;
printf "%s" (arbre_to_tex arbre_modus_tollens);;

print_subsection "Syllogisme disjonctif";;
let arbre_syllogisme_disjonctif =
	let syllogisme_disjonctif = [Or(p, q); Not(p)], q in
	let a,b,c = d_e syllogisme_disjonctif p q in
	let b1 = abs b in
	let b11, b12 = n_e b1 p in

	Noeud(Seq(syllogisme_disjonctif), [
		Feuille(Seq(a));
		Noeud(Seq(b), [
			Noeud(Seq(b1), [
				Feuille(Seq(b11));
				Feuille(Seq(b12))
			], N_E)
		], ABS);
		Feuille(Seq(c))
	], D_E);;
printf "%s" (arbre_to_tex arbre_syllogisme_disjonctif);;

print_subsection "Syllogisme barbara";;
let arbre_syllogisme_barbara =
	let syllogisme_barbara = [Impl(p, q); Impl(q, r)], Impl(p, r) in
	let a = i_i syllogisme_barbara in
	let b,c = i_e a q in
	Noeud(Seq(syllogisme_barbara), [
		Noeud(Seq(a), [
			Feuille(Seq(b));
			Noeud(Seq(c), [
				Feuille(Ref("Modus Ponens"))
			], V)
		], I_E)
	], I_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_barbara);;

print_subsection "Syllogisme Festino";;
let arbre_syllogisme_festino =
	let syllogisme_festino = [Impl(p, Not(q)); q], Not(p) in
	let a = n_i syllogisme_festino in
	let b,c = n_e a q in
	Noeud(Seq(syllogisme_festino), [
		Noeud(Seq(a), [
			Noeud(Seq(b), [
				 Feuille(Ref("Modus Ponens"))
			], V);
			Feuille(Seq(c))
		], N_E)
	], N_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_festino);;

print_subsection "Syllogisme Cesare";;
let arbre_syllogisme_cesare =
	let syllogisme_cesare = [Impl(p, Not(q)); Impl(r, q)], Impl(r, Not(p)) in
	let a = i_i syllogisme_cesare in
	let b = n_i a in
	let c,d = n_e b q in

	Noeud(Seq(syllogisme_cesare), [
		Noeud(Seq(a), [
			Noeud(Seq(b), [
				 Noeud(Seq(c), [
				   Feuille(Ref("Modus Ponens"))
				 ], V);
				Noeud(Seq(d), [
					Feuille(Ref("Modus Ponens"))
				], V)
			], N_E);
		], N_I)
	], I_I);;
printf "%s" (arbre_to_tex arbre_syllogisme_cesare);;



printf "\n\\end{document}"