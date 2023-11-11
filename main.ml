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
	| Phi -> "\\varphi"
	| Gamma -> "\\Gamma";;

type form =
| Var of var
| VarGreek of greek
| And of form * form
| Impl of form * form
| Or of form * form
| Not of form
| ForAll of form * form
| Exist of form * form
| Function of form * form list
| Vide
| Renomage of form * form
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
| A_I
| A_E
| E_I
| E_E
| ABS
| Aff
| V
| Info of rules * (form list);;

let rec tex_string_form (form:form) =
	match form with
	| Var(c) -> sprintf "%c" c
	| VarGreek(g) -> sprintf "%s" (tex_of_greek g)
	| And(f1,f2) -> sprintf "(%s \\wedge %s)" (tex_string_form f1) (tex_string_form f2)
	| Impl(f1,f2) -> sprintf "(%s \\rightarrow %s)" (tex_string_form f1) (tex_string_form f2)
	| Or(f1,f2) -> sprintf "(%s \\vee %s)" (tex_string_form f1) (tex_string_form f2)
	| Not(f) -> sprintf "\\neg %s" (tex_string_form f)
	| ForAll(v,f) -> sprintf "\\forall %s.%s" (tex_string_form v) (tex_string_form f)
	| Exist(v,f) -> sprintf "\\exists %s.%s" (tex_string_form v) (tex_string_form f)
	| Function(v, l) -> sprintf "%s(%s)" (tex_string_form v) (String.concat "," (List.map (fun x -> tex_string_form x) l))
	| Vide -> sprintf ""
	| Renomage (f1, f2) -> sprintf "[%s \\rightarrow %s]" (tex_string_form f1) (tex_string_form f2)
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
| A_I -> "\\forall_i"
| A_E -> "\\forall_e"
| E_I -> "\\exists_i"
| E_E -> "\\exists_e"
| ABS -> "\\bot"
| Aff -> "\\text{aff}"
| V -> " "
| Info(r, l) -> sprintf "%s \\textcolor{gray}{%s}" (tex_of_rule r) (String.concat " " (List.mapi (fun i x -> sprintf "%s{%s}" (if i=0 then "\\;" else ",") (tex_string_form x)) l));;

type arbre =
| Feuille of seq
| Noeud of seq * arbre list * rules
| FeuilleRef of string;;

let rec string_form (form: form) =
	(*with sprintf*)
	match form with
	| Var(c) -> sprintf "%c" c
	| VarGreek(g) -> sprintf "%s" (string_of_greek g)
	| And(f1,f2) -> sprintf "(%s /\\ %s)" (string_form f1) (string_form f2)
	| Impl(f1,f2) -> sprintf "(%s -> %s)" (string_form f1) (string_form f2)
	| Or(f1,f2) -> sprintf "(%s \\/ %s)" (string_form f1) (string_form f2)
	| Not(f) -> sprintf "¬%s" (string_form f)
	| ForAll(v,f) -> sprintf "∀%s.%s"  (string_form v) (string_form f)
	| Exist(v,f) -> sprintf "∃%s.%s"  (string_form v) (string_form f)
	| Function(v, l) -> sprintf "%s(%s)" (string_form v) (String.concat "," (List.map (fun x -> string_form x) l))
	| Vide -> sprintf ""
	| Renomage (f1, f2) -> sprintf "[%s -> %s]" (string_form f1) (string_form f2)
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

let affiche_seq (seq:seq) =
	printf "%s" (string_seq seq);;

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

let rec affiche_arbre ?(n=0) (a:arbre) =
	match a with
	| Feuille(seq) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"
	| Noeud(seq, l, _) -> printf "%s" (String.make (n*4) ' '); affiche_seq seq; printf "\n"; List.iter (fun x -> affiche_arbre ~n:(n+1) x) l
	| FeuilleRef(s) -> printf "%s" (String.make (n*4) ' '); printf "%s\n" s;;
let arbre_to_tex (a:arbre) =
	let list = ref [] in
	let rec aux (a:arbre) =
		match a with
		| Feuille(seq) when (ax seq) -> list := (sprintf "  \\AxiomC{} \\RightLabel{$\\text{ax}$} \\UnaryInfC{$%s$}\n" (tex_string_seq seq))::!list;
		| Feuille(seq) -> list := (sprintf "  \\AxiomC{} \\RightLabel{} \\UnaryInfC{$%s$}\n" (tex_string_seq seq))::!list;
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

let libre (x:form) (gamma:form list) =
    false;;

let rec is_form_libre (x:form) (phi: form) =
	match phi with
	| Var(_) -> false
	| VarGreek(_) -> false
	| And(phi1,phi2) -> (is_form_libre x phi1) || (is_form_libre x phi2)
	| Impl(phi1,phi2) -> (is_form_libre x phi1) || (is_form_libre x phi2)
	| Or(phi1,phi2) -> (is_form_libre x phi1) || (is_form_libre x phi2)
	| Not(phi1) -> (is_form_libre x phi1)
	| ForAll(y,phi1) when x = y -> false
	| ForAll(y,phi1) -> (is_form_libre x phi1)
	| Exist(y,phi1) when x = y -> false
	| Exist(y,phi1) -> (is_form_libre x phi1)
	| Function(y, l) -> List.exists (fun x -> is_form_libre x y) l
	| Vide -> false
	| Renomage(phi1, phi2) -> (is_form_libre x phi1) || (is_form_libre x phi2)
	| False -> false;;

let rec rien_libre (x:form) (gamma:form list) =
	match gamma with
	| [] -> true
	| f::l -> (not (is_form_libre x f)) && (rien_libre x l);;


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



let renomage ?(libre=false) (phi: form) (valx: form) (valt: form) =
	(*Renome que sur la porté du quantificateur*)
	let rec remplacement phi valx valt =
		match phi with
		| d when d = valx -> valt
		| Var(_) -> phi
		| VarGreek(_) -> phi
		| And(phi1,phi2) -> And(remplacement phi1 valx valt, remplacement phi2 valx valt)
		| Impl(phi1,phi2) -> Impl(remplacement phi1 valx valt, remplacement phi2 valx valt)
		| Or(phi1,phi2) -> Or(remplacement phi1 valx valt, remplacement phi2 valx valt)
		| Not(phi1) -> Not(remplacement phi1 valx valt)
		| ForAll(y,phi1) when valx = y -> ForAll(valt, remplacement phi1 valx valt)
		| ForAll(y,phi1) -> ForAll(y, remplacement phi1 valx valt)
		| Exist(y,phi1) when valx = y -> Exist(valt, remplacement phi1 valx valt)
		| Exist(y,phi1) -> Exist(y, remplacement phi1 valx valt)
		| Function(y, l) -> Function(y, List.map (fun x -> remplacement x valx valt) l)
		| Vide -> Vide
		| Renomage(phi1, phi2) -> Renomage(remplacement phi1 valx valt, remplacement phi2 valx valt)
		| False -> False
	and cherche_var phi valx valt =
		match phi with
		| Var(_) -> phi
		| VarGreek(_) -> phi
		| And(phi1,phi2) -> And(cherche_var phi1 valx valt, cherche_var phi2 valx valt)
		| Impl(phi1,phi2) -> Impl(cherche_var phi1 valx valt, cherche_var phi2 valx valt)
		| Or(phi1,phi2) -> Or(cherche_var phi1 valx valt, cherche_var phi2 valx valt)
		| Not(phi1) -> Not(cherche_var phi1 valx valt)
		| ForAll(y,phi1) when valx = y -> ForAll(valt, cherche_var phi1 valx valt)
		| ForAll(y,phi1) -> ForAll(y, cherche_var phi1 valx valt)
		| Exist(y,phi1) when valx = y -> Exist(valt, cherche_var phi1 valx valt)
		| Exist(y,phi1) -> Exist(y, cherche_var phi1 valx valt)
		| Function(y, l) -> Function(y, List.map (fun x -> cherche_var x valx valt) l)
		| Vide -> Vide
		| Renomage(phi1, phi2) -> Renomage(cherche_var phi1 valx valt, cherche_var phi2 valx valt)
		| False -> False
	in if libre then remplacement phi valx valt else cherche_var phi valx valt;;


let a_i (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| ForAll(x, phi1) when (rien_libre x gamma) -> (gamma, phi1)
	| ForAll(_, _) -> failwith "a_i : x is not free in gamma"
	| _ -> failwith "a_i : phi is not a universal quantification";;

let a_e (seq: seq) (x: form) =
	let gamma, phi = seq in
	(gamma, ForAll(x, phi));;

let ar_e (seq: seq) (x: form) (t: form) =
	let gamma, phi = seq in
	let newphi = renomage ~libre:true (ForAll(x, phi)) x t in
	(gamma, newphi);;

let e_i (seq: seq) =
	let gamma, phi = seq in
	match phi with
	| Exist(x, phi1) -> (gamma, phi1)
	| _ -> failwith "e_i : phi is not an existential quantification";;

let er_i (seq: seq) (t: form) =
	let gamma, phi = seq in
	match phi with
	| Exist(x, phi1) -> x, (gamma, renomage ~libre:true phi1 x t)
	| _ -> failwith "er_i : phi is not an existential quantification";;

let e_e (seq: seq) (x: form) (phi: form) =
	let gamma, psi = seq in
	if not (rien_libre x [psi]) then failwith "e_e : x is not free in psi";
	if not (rien_libre x gamma) then failwith "e_e : x is not free in gamma";
	(gamma, Exist(x,phi)), (phi::gamma, psi);;








let p = Var('p');;
let q = Var('q');;
let r = Var('r');;
let x = Var('x');;
let y = Var('y');;
let z = Var('z');;
let phi = VarGreek(Phi);;


let print_section (title: string) =
	printf "\n\\section{%s}\n" title;;
let print_subsection (title: string) =
	printf "\n\\subsection{%s}\n" title;;


printf "%s" (
"\\input{packages.tex}"^
"\n\\begin{document}"^
"\n\\maketitle"^
"\n\\begin{center}\\LARGE{\\textcolor{red}{Ce document contient des coquilles, des erreurs et des fautes d'orthographe. Merci de me les signaler par \\href{http://www.github.com/ARKANYOTA/ProofTreeOcaml}{Github}/message discord/\\href{mailto:arkanyota@icloud.com}{mail}.}}\\end{center}"^
"\n\\begin{center}\\large{Vous pouvez aussi m'aider à remplir ce document. ;)}\\end{center}"^
"\n\\tableofcontents"
);;

print_section "Cours";;
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
				FeuilleRef("Modus Ponens")
			], V);
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

print_subsection "Tiers Exclu";;
let arbre_tiers_exclu =
	let tiers_exclu = [],Or(Not(p), p) in
	let t1 = abs tiers_exclu in
	let t11, t12 = n_e t1 p in
	let t111 = n_i t11 in
	let t1111, t1112 = n_e t111 (Or(Not(p), p)) in
	let t11121 = d_id t1112 in
	Noeud(tiers_exclu,[
		 Noeud(t1,[
			 Noeud(t11,[
				 Noeud(t111, [
					  Feuille(t1111);
						Noeud(t1112, [
							Feuille(t11121)
						], D_ID)
				 ], Info(N_E, [Or(Not(p), p)]));
			 ],N_I);
			 Noeud(t12,[FeuilleRef("Idem")],ABS)
		 ],N_E)
	],N_I);;
printf "%s" (arbre_to_tex arbre_tiers_exclu);;

print_section "Exercices";;

print_subsection "Exo 13.1";;
let exo13_2 =
	let seq = [ForAll (x, phi)], Exist (x, phi) in
	let seq1 = e_i seq in
	let seq11 = a_e seq1 x in
	Noeud(seq,[
		 Noeud(seq1, [
			 Feuille(seq11)
		 ], Info(A_E,[x]));
	],E_I);;
printf "%s" (arbre_to_tex exo13_2);;

print_subsection "Exo 13.2";;
let exo13_2 =
	let seq = [Exist (z, ForAll (x, Function(phi, [z; x])))], ForAll (y, Exist (x, Function(phi, [x; y]))) in
	let seq1, seq2 = e_e seq z (ForAll (x, Function(phi, [z; x]))) in
	let seq21 = a_i seq2 in
	let x, seq211 = er_i seq21 z in
	let seq2111 = ar_e seq211 y x in
	Noeud(seq,[
			Feuille(seq1);
			Noeud(seq2, [
				Noeud(seq21, [
					Noeud(seq211,[
						Feuille(seq2111)
					], Info(A_E, [Renomage(y,x)]))
				], Info(E_I,[Renomage(x,y)]));
			], A_I)
	], Info(E_E,[x; Function(phi, [z; x])]));;
printf "%s" (arbre_to_tex exo13_2);;



printf "\n\\end{document}"