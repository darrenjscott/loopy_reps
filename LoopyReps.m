(* ::Package:: *)

BeginPackage["LoopyReps`"]


(* Define functions + variables *)
int0::usage = "Sets integrals which are genuinely zero in dim reg \
(and not just a cancelation between a UV and IR pole) to zero. \
Should generally be used first."

intCancel::usage = "Replaces particularly simple integrals in terms of others\
which might aid in cancelations and simplifying an answer while retaining it \
in terms of PV integrals."

intDiv::usage = "Replaces loop integrals by their divergent parts \
and a function which holds the finite remainder. E.g. it makes the replacement \
B0i[bb0,p2,m02,m12] -> 1/eUV + B0iFin[bb0,p2,m02,m12]. \
Note that we retain information on whether the poles are UV or IR, \
so some scaleless integrals are replaced by a/eUV - a/eIR for some constant a."

intFin::usage = "Replaces the finite part of the integrals with their analytic expressions."

localFix::usage = "Function to deal with the Dminus4 terms when using Dimension->0.  \
Replaces terms like Dminus4/eUV -> -2 etc. As in FormCalc, they are tagged with Finite \
which can be set to 1. WARNING: Function probably not full-proof, \
but should deal with up to double poles. The Finite tag can be used to help \
debug this if necessary."

localFix2::usage = "Alternative implementation of localFix. Can be used for testing."

discRep::usgae = "Function for replacing the DiscB terms by their actual analytic \
expressions. "

scalarC0Rep::usage = "Function for replacing ScalarC0[...] terms by their analytic \
expressions. WARNING: Does not include all cases yet."



A0Fin::usage = "Finite part of the A0 integral";
B0iFin::usage = "Finite part of the B0i integral";
C0iFin::usage = "Finite part of the C0i integral";
D0iFin::usage = "Finite part of the D0i integral";

DiscB::usage = "Part of the B0 integral containing the s-plane branch-cut (lifted from Package-X)";
ScalarC0::usage = "Scalar C0, but for real invariants (lifted from Package-X)"
DiLog::usage = "\!\(\*SubscriptBox[\(Li\), \(2\)]\)[x], but depends on the sign of the SECOND ARGUMENT if x>1.\
See package-X documentation if you're worried about the sign of the imaginary part."
(* Variables *)
eUV::usage = "Epsilon used in the regulation of a UV pole";
eIR::usage = "Epsilon used in the regulation of an IR pole";
\[Mu]::usage = "Mu scale which arises in dim-reg";

(* TAGS *)
tagIM::usage = "Just a tag for pieces of integrals which are explicitly imaginary.";



Begin["`Private`"]


$LoopyRepsVersion = "LoopyReps 0.8 (07 June 2023)"

Print[""];
Print[$LoopyRepsVersion];
Print["by Darren Scott"];
Print["WARNING: Many integral substitutions are still missing \
and those that are here may yet still contain mistakes. Just be careful. \
The analytic solutions for the integrals have been taken from Package-X, and from \
explicit calculation for derivative integrals."];
Print["IMPORTANT: You must load FormCalc FIRST in order to be able to use this."];


(* Some objects in here have to be indentified with the same objects in other \
contexts outside this pacakge. *)
Amp=FormCalc`Amp;

A0[x__]:=LoopTools`A0[x];
B0i[x__]:=LoopTools`B0i[x];
C0i[x__]:=LoopTools`C0i[x];
D0i[x__]:=LoopTools`D0i[x];

bb0:=LoopTools`bb0;
bb1:=LoopTools`bb1;
bb00:=LoopTools`bb00;
bb11:=LoopTools`bb11;
bb001:=LoopTools`bb001;

dbb0:=LoopTools`dbb0;
dbb1:=LoopTools`dbb1;
dbb00:=LoopTools`dbb00;
dbb11:=LoopTools`dbb11;

cc0:=LoopTools`cc0;
cc1:=LoopTools`cc1;
cc2:=LoopTools`cc2;
cc00:=LoopTools`cc00;
cc11:=LoopTools`cc11;
cc12:=LoopTools`cc12;
cc22:=LoopTools`cc22;
cc001:=LoopTools`cc001;
cc002:=LoopTools`cc002;
cc112:=LoopTools`cc112;
cc122:=LoopTools`cc122;
cc222:=LoopTools`cc222;

dd0:=LoopTools`dd0;
dd1:=LoopTools`dd1;
dd2:=LoopTools`dd2;
dd3:=LoopTools`dd3;
dd00:=LoopTools`dd00;
dd11:=LoopTools`dd11;
dd12:=LoopTools`dd12;
dd13:=LoopTools`dd13;
dd22:=LoopTools`dd22;
dd23:=LoopTools`dd23;
dd33:=LoopTools`dd33;



Dminus4:=FormCalc`Dminus4;
Finite:=FormCalc`Finite;
(* Not sure why I have to do the following, but I had issues..*)
(*MH2:=FormCalc`MH2;*)


(* Checks that none of the arguments are actually zero \
avoids problems with missing integrals, or whatever...*)
(* UPDATED: To check none of the masses are the same. "Union" shortens the list \
for repeated elements. So the lists will be a different size if there is a repeat \
and the function will return false. *)
zeroChecks[vars_] := And[And@@((#=!=0)&/@vars),Length[Union[vars]]==Length[vars]];


(* This function could probably be written better, not sure if it is sufficient... *)
localFix2[expr_]:=Block[{tmp,rt1,rt11,rt2,rt3,a,b},
tmp=ExpandAll[expr]/.eUV->eUV/a/. eIR->eIR/a/. Dminus4->b Dminus4;
rt1=Coefficient[Coefficient[tmp,b,1],a,1]/.eUV->1/.eIR->1/.Dminus4->-2;
rt11=Coefficient[Coefficient[tmp,b,1],a,2]/.eUV->1/.eIR->1/.Dminus4->-(2/eIR);
rt2=Coefficient[Coefficient[tmp,b,2],a,2]/.eUV->1/.eIR->1/.Dminus4->-2;
rt3=Coefficient[Coefficient[tmp,b,2],a,1]/.Dminus4->-2eIR;
(* rt3 not actually needed *)
(expr/.Dminus4->0)+ Finite rt1 + Finite rt11 + Finite^2 rt2
];

localFix[expr_]:=Block[{tmp2,tmp,dd,dd1,dd2,uv1,ir1,ir2,fnt,fin},
tmp2=If[Head[Head[expr]]===Amp,Plus@@expr,expr];
tmp=ExpandAll[ExpandAll[tmp2/.Conjugate[Dminus4]->Dminus4/.Conjugate[eUV]->eUV/.Conjugate[eIR]->eIR]];
dd1=Coefficient[tmp,Dminus4,1]Dminus4;
dd2=Coefficient[tmp,Dminus4,2]Dminus4^2;
dd=dd1+dd2;
uv1=Collect[Coefficient[dd,eUV,-1] 1/eUV/.Dminus4->-2eUV,eUV];
ir1=Collect[Coefficient[dd,eIR,-1] 1/eIR/.Dminus4->-2eIR,eIR];
ir2=Collect[Coefficient[dd,eIR,-2] 1/eIR^2/.Dminus4->-2eIR,eIR];
fin=(tmp2/. Dminus4->0)+ Finite(uv1+ir1+ir2);
If[Head[Head[expr]]===Amp,Head[expr][fin],fin]
];


int0Reps = {
B0i[bb00,0,0,0]->0,
Dminus4 B0i[bb1,0,0,0]->0
};


intCancelReps = {
B0i[bb0,0,0,m12_]:>1/m12 A0[m12]/; zeroChecks[{m12}],
B0iFin[bb0,0,0,m12_]:>1/m12 A0Fin[m12]/; zeroChecks[{m12}],

B0i[bb1,0,0,m12_]:>1/4 - 1/(2m12) A0[m12]/; zeroChecks[{m12}],
B0iFin[bb1,0,0,m12_]:>1/4 - 1/(2m12) A0Fin[m12]/; zeroChecks[{m12}],

B0i[bb1,m12_,m22_,m22_]:>-1/2 B0i[bb0,m12,m22,m22]/; zeroChecks[{m12,m22}],
B0iFin[bb1,m12_,m22_,m22_]:>-1/2 B0iFin[bb0,m12,m22,m22]/; zeroChecks[{m12,m22}],

C0i[cc2,0,m12_,0,0,0,0]:>C0i[cc1,0,m12,0,0,0,0]/; zeroChecks[{m12}],
C0iFin[cc2,0,m12_,0,0,0,0]:>C0iFin[cc1,0,m12,0,0,0,0]/; zeroChecks[{m12}],

C0i[cc2,0,0,0,0,m12_,m12_]:>C0i[cc1,0,0,0,0,m12,m12]/; zeroChecks[{m12}],
C0iFin[cc2,0,0,0,0,m12_,m12_]:>C0iFin[cc1,0,0,0,0,m12,m12]/; zeroChecks[{m12}],

C0i[cc0,0,0,m12_,0,0,m12_]:>C0i[cc0,0,m12,0,0,0,m12]/; zeroChecks[{m12}],
C0iFin[cc0,0,0,m12_,0,0,m12_]:>C0iFin[cc0,0,m12,0,0,0,m12]/; zeroChecks[{m12}],

C0i[cc2,m12_,0,m12_,0,0,0]:>C0i[cc1,m12,0,m12,0,0,0]/; zeroChecks[{m12}],
C0iFin[cc2,m12_,0,m12_,0,0,0]:>C0iFin[cc1,m12,0,m12,0,0,0]/; zeroChecks[{m12}],

C0i[cc2,0,m12_,0,0,m12_,m12_]:>C0i[cc1,0,m12,0,0,m12,m12]/; zeroChecks[{m12}],
C0iFin[cc2,0,m12_,0,0,m12_,m12_]:>C0iFin[cc1,0,m12,0,0,m12,m12]/; zeroChecks[{m12}],

C0i[cc122,0,m12_,0,0,0,m12_]:>1/4 C0i[cc112,0,m12,0,0,0,m12]/; zeroChecks[{m12}],
C0iFin[cc122,0,m12_,0,0,0,m12_]:>1/4 C0iFin[cc112,0,m12,0,0,0,m12]/; zeroChecks[{m12}],

C0i[cc0,0,m12_,m22_,0,0,0]:>C0i[cc0,m12,0,m22,0,0,0]/; zeroChecks[{m12}],
C0iFin[cc0,0,m12_,m22_,0,0,0]:>C0iFin[cc0,m12,0,m22,0,0,0]/; zeroChecks[{m12}],

C0i[cc2,0,m12_,0,0,m22_,m22_]:>C0i[cc1,0,m12,0,0,m22,m22]/; zeroChecks[{m12,m22}],
C0iFin[cc2,0,m12_,0,0,m22_,m22_]:>C0iFin[cc1,0,m12,0,0,m22,m22]/; zeroChecks[{m12,m22}],

C0i[cc22,0,0,m12_,0,0,m12_]:>C0i[cc12,0,0,m12,0,0,m12]/; zeroChecks[{m12}],
C0iFin[cc22,0,0,m12_,0,0,m12_]:>C0iFin[cc12,0,0,m12,0,0,m12]/; zeroChecks[{m12}],

C0i[cc122,0,0,m12_,0,0,m12_]:>1/2 * C0i[cc112,0,0,m12,0,0,m12]/; zeroChecks[{m12}],
C0iFin[cc122,0,0,m12_,0,0,m12_]:>1/2 * C0iFin[cc112,0,0,m12,0,0,m12]/; zeroChecks[{m12}],

C0i[cc222,0,0,m12_,0,0,m12_]:>C0i[cc112,0,0,m12,0,0,m12]/; zeroChecks[{m12}],
C0iFin[cc222,0,0,m12_,0,0,m12_]:>C0iFin[cc112,0,0,m12,0,0,m12]/; zeroChecks[{m12}],

C0i[cc002,0,m12_,0,0,m22_,m22_]:>C0i[cc001,0,m12,0,0,m22,m22]/; zeroChecks[{m12,m22}],
C0iFin[cc002,0,m12_,0,0,m22_,m22_]:>C0iFin[cc001,0,m12,0,0,m22,m22]/; zeroChecks[{m12,m22}],

D0i[dd12,0,0,0,0,0,0,0,0,0,m12_]:>1/2 D0i[dd11,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
D0iFin[dd12,0,0,0,0,0,0,0,0,0,m12_]:>1/2 D0iFin[dd11,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],

D0i[dd23,0,0,0,0,0,0,0,0,0,m12_]:>D0i[dd13,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
D0iFin[dd23,0,0,0,0,0,0,0,0,0,m12_]:>D0iFin[dd13,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}]

};


intDivReps = {
(* A0 Integral - Divergence only *)
A0[m12_]:>m12/eUV+A0Fin[m12]/;zeroChecks[{m12}],

(************************************)
(* B0i integrals - Divergences only *)
(************************************)

(* Scaleless *)
B0i[bb0,0,0,0]->1/eUV-1/eIR, (* Double checked *)
B0i[bb1,0,0,0]->1/(2eIR)-1/(2eUV),
B0i[dbb00,0,0,0]->1/(12eIR)-1/(12eUV),

(* One scale *)
B0i[bb0,p12_,0,0]:>1/eUV+B0iFin[bb0,p12,0,0]/;zeroChecks[{p12}], 
B0i[bb1,p12_,0,0]:>-1/(2 eUV)+B0iFin[bb1,p12,0,0]/;zeroChecks[{p12}], (* Double checked *)
B0i[bb00,p12_,0,0]:>-(p12/(12 eUV))+B0iFin[bb00,p12,0,0]/;zeroChecks[{p12}], 
B0i[bb11,p12_,0,0]:>1/(3eUV)+B0iFin[bb11,p12,0,0]/;zeroChecks[{p12}],
B0i[dbb0,p12_,0,0]:>B0iFin[dbb0,p12,0,0]/;zeroChecks[{p12}],
B0i[dbb1,p12_,0,0]:>B0iFin[dbb1,p12,0,0]/;zeroChecks[{p12}], (* Double checked *)
B0i[dbb00,p12_,0,0]:>-(1/(12eUV))+B0iFin[dbb00,p12,0,0]/;zeroChecks[{p12}], (* Double checked *)
B0i[dbb11,p12_,0,0]:>B0iFin[dbb11,p12,0,0]/;zeroChecks[{p12}],

(* Note: FormCalc automatically replaces the bb0 and dbb0 integrals with only one *)
(* non-zero mass, by the same integral with the mass at the end argument (due to symmetry). *)
(* Therefore these will be picked up later *)
(*B0i[bb0,0,m12_,0]:>WARNING/;zeroChecks[{m12}],*)
B0i[bb1,0,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[bb00,0,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[bb11,0,m12_,0]:>WARNING/;zeroChecks[{m12}],
(*B0i[dbb0,0,m12_,0]:>WARNING/;zeroChecks[{m12}],*)
B0i[dbb1,0,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[dbb00,0,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[dbb11,0,m12_,0]:>WARNING/;zeroChecks[{m12}],

B0i[bb0,0,0,m12_]:>1/eUV+B0iFin[bb0,0,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[bb1,0,0,m12_]:>-(1/(2eUV))+B0iFin[bb1,0,0,m12]/;zeroChecks[{m12}],
B0i[bb00,0,0,m12_]:>m12/(4 eUV)+B0iFin[bb00,0,0,m12]/;zeroChecks[{m12}],
B0i[bb11,0,0,m12_]:>WARNING/;zeroChecks[{m12}],
B0i[dbb0,0,0,m12_]:>B0iFin[dbb0,0,0,m12]/;zeroChecks[{m12}],
B0i[dbb1,0,0,m12_]:>WARNING/;zeroChecks[{m12}],
B0i[dbb00,0,0,m12_]:>-1/(12eUV)+B0iFin[dbb00,0,0,m12]/;zeroChecks[{m12}],
B0i[dbb11,0,0,m12_]:>WARNING/;zeroChecks[{m12}],

(*NOTE: bb0 and dbb0 integrals are covered by m12,0,m12, since FormCalc always re-orders the \
last two arguments to be "ordered". B0i[bb0,m12,m12,0] always IMMEDIATELY UPON WRITING\
gets converted to B0i[bb0,m12,0,m12]. So the rules will never catch it. *)
(*B0i[bb0,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],*)
B0i[bb1,m12_,m12_,0]:>-(1/(2 eUV))+B0iFin[bb1,m12,m12,0]/;zeroChecks[{m12}],
B0i[bb00,m12_,m12_,0]:>m12/(6 eUV)+B0iFin[bb00,m12,m12,0]/;zeroChecks[{m12}],
B0i[bb11,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],
(*B0i[dbb0,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],*)
B0i[dbb1,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[dbb00,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],
B0i[dbb11,m12_,m12_,0]:>WARNING/;zeroChecks[{m12}],


B0i[bb0,m12_,0,m12_]:>1/eUV+B0iFin[bb0,m12,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[bb1,m12_,0,m12_]:>-(1/(2eUV))+B0iFin[bb1,m12,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[bb00,m12_,0,m12_]:>m12/(6 eUV)+B0iFin[bb00,m12,0,m12]/;zeroChecks[{m12}],
B0i[bb11,m12_,0,m12_]:> 1/(3eUV)+B0iFin[bb11,m12,0,m12]/;zeroChecks[{m12}],
B0i[dbb0,m12_,0,m12_]:>-(1/(2 eIR m12))+B0iFin[dbb0,m12,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[dbb1,m12_,0,m12_]:>B0iFin[dbb1,m12,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[dbb00,m12_,0,m12_]:>-(1/(12eUV))+B0iFin[dbb00,m12,0,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[dbb11,m12_,0,m12_]:>B0iFin[dbb11,m12,0,m12]/;zeroChecks[{m12}],

B0i[bb0,0,m12_,m12_]:>1/eUV+B0iFin[bb0,0,m12,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[bb1,0,m12_,m12_]:> -(1/(2 eUV))+B0iFin[bb1,0,m12,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[bb00,0,m12_,m12_]:>m12/(2eUV)+B0iFin[bb00,0,m12,m12]/;zeroChecks[{m12}],
B0i[bb11,0,m12_,m12_]:>WARNING/;zeroChecks[{m12}],
B0i[dbb0,0,m12_,m12_]:>B0iFin[dbb0,0,m12,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[dbb1,0,m12_,m12_]:>WARNING/;zeroChecks[{m12}],
B0i[dbb00,0,m12_,m12_]:>-(1/(12 eUV))+B0iFin[dbb00,0,m12,m12]/;zeroChecks[{m12}], (* Double checked *)
B0i[dbb11,0,m12_,m12_]:>WARNING/;zeroChecks[{m12}],


(* TWO SCALES *)
(*NOTE: bb0 and dbb0 integrals are covered by m12,0,m22, since FormCalc always re-orders the \
last two arguments to be "ordered". B0i[bb0,m12,m22,0] always IMMEDIATELY UPON WRITING\
gets converted to B0i[bb0,m12,0,m22]. So the rules will never catch it. *)
(*B0i[bb0,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],*)
B0i[bb1,m12_,m22_,0]:>-(1/(2 eUV))+B0iFin[bb1,m12,m22,0]/;zeroChecks[{m12,m22}],
B0i[bb00,m12_,m22_,0]:>-((m12-3 m22)/(12 eUV))+B0iFin[bb00,m12,m22,0]/;zeroChecks[{m12,m22}],
B0i[bb11,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],
(*B0i[dbb0,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],*)
B0i[dbb1,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],
B0i[dbb00,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],
B0i[dbb11,m12_,m22_,0]:>WARNING/;zeroChecks[{m12,m22}],


B0i[bb0,m12_,0,m22_]:>1/eUV+B0iFin[bb0,m12,0,m22]/;zeroChecks[{m12,m22}],  (* Double checked *)
B0i[bb1,m12_,0,m22_]:>-(1/(2eUV))+B0iFin[bb1,m12,0,m22]/;zeroChecks[{m12,m22}],  (* Double checked *)
B0i[bb00,m12_,0,m22_]:>-((m12-3 m22)/(12 eUV))+B0iFin[bb00,m12,0,m22]/;zeroChecks[{m12,m22}],
B0i[bb11,m12_,0,m22_]:>1/(3 eUV)+B0iFin[bb11,m12,0,m22]/;zeroChecks[{m12,m22}],
B0i[dbb0,m12_,0,m22_]:>B0iFin[dbb0,m12,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb1,m12_,0,m22_]:>B0iFin[dbb1,m12,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb00,m12_,0,m22_]:>-(1/(12 eUV))+B0iFin[dbb00,m12,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb11,m12_,0,m22_]:>B0iFin[dbb11,m12,0,m22]/;zeroChecks[{m12,m22}],

B0i[bb0,0,m12_,m22_]:>1/eUV+B0iFin[bb0,0,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb1,0,m12_,m22_]:>-(1/(2 eUV))+B0iFin[bb1,0,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb00,0,m12_,m22_]:>(m12+m22)/(4 eUV)+B0iFin[bb00,0,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb11,0,m12_,m22_]:>WARNING/;zeroChecks[{m12,m22}],
B0i[dbb0,0,m12_,m22_]:>B0iFin[dbb0,0,m12,m22]/;zeroChecks[{m12,m22}],
B0i[dbb1,0,m12_,m22_]:>WARNING/;zeroChecks[{m12,m22}],
B0i[dbb00,0,m12_,m22_]:>-1/(12eUV)+B0iFin[dbb00,0,m12,m22]/;zeroChecks[{m12,m22}],
B0i[dbb11,0,m12_,m22_]:>WARNING/;zeroChecks[{m12,m22}],


B0i[bb0,m12_,m12_,m22_]:>1/eUV+B0iFin[bb0,m12,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[bb1,m12_,m12_,m22_]:>-1/(2 eUV)+B0iFin[bb1,m12,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[bb00,m12_,m12_,m22_]:>(2 m12+3 m22)/(12 eUV)+B0iFin[bb00,m12,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb11,m12_,m12_,m22_]:>1/(3eUV)+B0iFin[bb11,m12,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb001,m12_,m12_,m22_]:>-((m12+4 m22)/(24 eUV))+B0iFin[bb001,m12,m12,m22]/;zeroChecks[{m12,m22}],
B0i[dbb0,m12_,m12_,m22_]:>B0iFin[dbb0,m12,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb1,m12_,m12_,m22_]:>B0iFin[dbb1,m12,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb00,m12_,m12_,m22_]:>-(1/(12 eUV))+B0iFin[dbb00,m12,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb11,m12_,m12_,m22_]:>B0iFin[dbb11,m12,m12,m22]/;zeroChecks[{m12,m22}],

(*NOTE: bb0 and dbb0 integrals have their arguments re-numbered. This is because FormCalc \
always re-orders the last two arguments to be "ordered" (alphabetically). B0i[bb0,m12,m22,m12] always IMMEDIATELY UPON WRITING\
gets converted to B0i[bb0,m12,m12,m22]. So the rules will never catch it if the arguments are something like [MW2, MH2, MW2] \
since there the last two are already ordered. It is therefore necessary to write the rules themselves, so that the last two \
pattern matching expressions are themselves already ordered. Hence the first mass scale in the bb0 and dbb0 integrals is named \
m22 and not m12 as is convention everywhere else. Cases like [MW2,MZ2,MW2] get converted to [MW2,MW2,MZ2] and are captured \
by the rules above. \
The re-ordering happens only for the bb0 and dbb0 integrals, so the others can be left as they are. *)
B0i[bb0,m22_,m12_,m22_]:>1/eUV+B0iFin[bb0,m22,m12,m22]/;zeroChecks[{m12,m22}],
B0i[bb1,m12_,m22_,m12_]:>-(1/(2eUV))+B0iFin[bb1,m12,m22,m12]/;zeroChecks[{m12,m22}],
B0i[bb00,m12_,m22_,m12_]:>(2m12+3 m22)/(12 eUV)+B0iFin[bb00,m12,m22,m12]/;zeroChecks[{m12,m22}],
B0i[bb11,m12_,m22_,m12_]:>1/(3eUV)+B0iFin[bb11,m12,m22,m12]/;zeroChecks[{m12,m22}],
B0i[dbb0,m22_,m12_,m22_]:>B0iFin[dbb0,m22,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb1,m12_,m22_,m12_]:>B0iFin[dbb1,m12,m22,m12]/;zeroChecks[{m12,m22}],
B0i[dbb00,m12_,m22_,m12_]:>-(1/(12 eUV))+B0iFin[dbb00,m12,m22,m12]/;zeroChecks[{m12,m22}], (* Double checked *)
B0i[dbb11,m12_,m22_,m12_]:>B0iFin[dbb11,m12,m22,m12]/;zeroChecks[{m12,m22}],

B0i[bb0,m12_,m22_,m22_]:>1/eUV+B0iFin[bb0,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[bb1,m12_,m22_,m22_]:>-(1/(2 eUV))+B0iFin[bb1,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[bb00,m12_,m22_,m22_]:>-((m12-6 m22)/(12 eUV))+B0iFin[bb00,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[bb11,m12_,m22_,m22_]:>1/(3 eUV)+B0iFin[bb11,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[dbb0,m12_,m22_,m22_]:> B0iFin[dbb0,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[dbb1,m12_,m22_,m22_]:> B0iFin[dbb1,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[dbb00,m12_,m22_,m22_]:> -1/(12 eUV) + B0iFin[dbb00,m12,m22,m22]/;zeroChecks[{m12,m22}],
B0i[dbb11,m12_,m22_,m22_]:> B0iFin[dbb11,m12,m22,m22]/;zeroChecks[{m12,m22}],


(* Three scales *)
B0i[bb0,m12_,m22_,m32_]:>1/eUV+B0iFin[bb0,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[bb1,m12_,m22_,m32_]:>-(1/(2 eUV))+B0iFin[bb1,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[bb00,m12_,m22_,m32_]:>-((m12-3 (m22+m32))/(12 eUV))+B0iFin[bb00,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[bb11,m12_,m22_,m32_]:>1/(3 eUV)+B0iFin[bb11,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[bb001,m12_,m22_,m32_]:>(m12-2 (m22+2 m32))/(24 eUV)+B0iFin[bb001,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],

B0i[dbb0,m12_,m22_,m32_]:>B0iFin[dbb0,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[dbb1,m12_,m22_,m32_]:>WARNING/;zeroChecks[{m12,m22,m32}],
B0i[dbb00,m12_,m22_,m32_]:>-(1/(12 eUV))+B0iFin[dbb00,m12,m22,m32]/;zeroChecks[{m12,m22,m32}],
B0i[dbb11,m12_,m22_,m32_]:>WARNING/;zeroChecks[{m12,m22,m32}],

(***********************************)
(* C0i integrals - Divergences only *)
(***********************************)
(* Scaleless *)
C0i[cc00,0,0,0,0,0,0]->1/(4eUV)-1/(4eIR),

(* One scale *)
C0i[cc0,m12_,0,0,0,0,0]:>1/(eIR^2 m12)+Log[-(\[Mu]^2/m12)]/(eIR m12)+C0iFin[cc0,m12,0,0,0,0,0]/;zeroChecks[{m12}],

C0i[cc0,0,0,0,0,0,m12_]:>1/(eIR m12)+C0iFin[cc0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc00,0,0,0,0,0,m12_]:>1/4 (1/eUV)+C0iFin[cc00,0,0,0,0,0,m12]/;zeroChecks[{m12}],

C0i[cc0,0,m12_,0,0,0,0]:>1/(eIR^2 m12)+Log[-(\[Mu]^2/m12)]/(eIR m12)+C0iFin[cc0,0,m12,0,0,0,0]/;zeroChecks[{m12}],
C0i[cc1,0,m12_,0,0,0,0]:>1/(eIR m12)+C0iFin[cc1,0,m12,0,0,0,0]/;zeroChecks[{m12}],
(*C0i[cc2,0,m12_,0,0,0,0]:>+C0iFin[cc2,0,m12,0,0,0,0]/;zeroChecks[{m12}], covered by cc1*)
C0i[cc00,0,m12_,0,0,0,0]:>1/(4 eUV)+C0iFin[cc00,0,m12,0,0,0,0]/;zeroChecks[{m12}],
C0i[cc11,0,m12_,0,0,0,0]:>-(1/(2 eIR m12))+C0iFin[cc11,0,m12,0,0,0,0]/;zeroChecks[{m12}],
C0i[cc12,0,m12_,0,0,0,0]:>C0iFin[cc12,0,m12,0,0,0,0]/;zeroChecks[{m12}],


C0i[cc0,0,0,m12_,0,0,0]:>1/(eIR^2 m12)+Log[-(\[Mu]^2/m12)]/(eIR m12)+C0iFin[cc0,0,0,m12,0,0,0]/;zeroChecks[{m12}],
C0i[cc1,0,0,m12_,0,0,0]:>-(1/(eIR^2 m12))+(-(2/m12)-Log[-(\[Mu]^2/m12)]/m12)/eIR+C0iFin[cc1,0,0,m12,0,0,0]/;zeroChecks[{m12}],
C0i[cc2,0,0,m12_,0,0,0]:>1/(eIR m12)+C0iFin[cc2,0,0,m12,0,0,0]/;zeroChecks[{m12}],
C0i[cc00,0,0,m12_,0,0,0]:>1/(4 eUV)+C0iFin[cc00,0,0,m12,0,0,0]/;zeroChecks[{m12}],

C0i[cc0,m12_,0,0,0,0,m12_]:>C0iFin[cc0,m12,0,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc00,m12_,0,0,0,0,m12_]:>1/(4 eUV)+C0iFin[cc00,m12,0,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc1,m12_,0,0,0,0,m12_]:>C0iFin[cc1,m12,0,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc2,m12_,0,0,0,0,m12_]:>C0iFin[cc2,m12,0,0,0,0,m12]/;zeroChecks[{m12}],

C0i[cc0,0,0,m12_,0,0,m12_]:>-(1/(2 eIR^2 m12))-Log[\[Mu]^2/m12]/(2 eIR m12)+C0iFin[cc0,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc1,0,0,m12_,0,0,m12_]:>-(1/(eIR m12))+C0iFin[cc1,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc2,0,0,m12_,0,0,m12_]:>C0iFin[cc2,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc00,0,0,m12_,0,0,m12_]:>1/(4 eUV)+C0iFin[cc00,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc12,0,0,m12_,0,0,m12_]:>C0iFin[cc12,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
(*C0i[cc22,0,0,m12_,0,0,m12_]:>+C0iFin[cc22,0,0,m12,0,0,m12]/;zeroChecks[{m12}],*) (* covered by c12*)
C0i[cc001,0,0,m12_,0,0,m12_]:>-(1/(12 eUV))+C0iFin[cc001,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc002,0,0,m12_,0,0,m12_]:>-(1/(12 eUV))+C0iFin[cc002,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc112,0,0,m12_,0,0,m12_]:>C0iFin[cc112,0,0,m12,0,0,m12]/;zeroChecks[{m12}],
(*C0i[cc122,0,0,m12_,0,0,m12_]:>C0iFin[cc122,0,0,m12,0,0,m12]/;zeroChecks[{m12}],*) (* covered by 112 *)
(*C0i[cc222,0,0,m12_,0,0,m12_]:>C0iFin[cc222,0,0,m12,0,0,m12]/;zeroChecks[{m12}],*) (* covered by 112 *)

C0i[cc0,0,0,0,0,m12_,m12_]:>C0iFin[cc0,0,0,0,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc00,0,0,0,0,m12_,m12_]:>1/4 (1/eUV)+C0iFin[cc00,0,0,0,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc1,0,0,0,0,m12_,m12_]:> C0iFin[cc1,0,0,0,0,m12,m12]/;zeroChecks[{m12}],
(*C0i[cc2,0,0,0,0,m12_,m12_]:> C0iFin[cc1,0,0,0,0,m12,m12]/;zeroChecks[{m12}] (* Covered by cc1 *)*)

(*C0i[cc0,0,0,m12_,0,0,m12_] SAME AS C0i[cc0,0,m12_,0,0,0,m12_]*)

C0i[cc1,m12_,0,m12_,0,0,0]:>1/(2 eIR m12)+C0iFin[cc1,m12,0,m12,0,0,0]/;zeroChecks[{m12}],
(* C0i[cc2,m12_,0,m12_,0,0,0] (* Covered by cc1*)*)

C0i[cc0,0,m12_,0,0,0,m12_]:>-(1/(2 eIR^2 m12))-Log[\[Mu]^2/m12]/(2 eIR m12)+C0iFin[cc0,0,m12,0,0,0,m12]/;zeroChecks[{m12}], (* Double checked *)
C0i[cc1,0,m12_,0,0,0,m12_]:>1/(2 eIR^2 m12)+(1/m12+Log[\[Mu]^2/m12]/(2 m12))/eIR+C0iFin[cc1,0,m12,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc2,0,m12_,0,0,0,m12_]:>C0iFin[cc2,0,m12,0,0,0,m12]/;zeroChecks[{m12}], (* Double checked *)
C0i[cc00,0,m12_,0,0,0,m12_]:>1/(4 eUV)+C0iFin[cc00,0,m12,0,0,0,m12]/;zeroChecks[{m12}], (* Double checked *)
C0i[cc11,0,m12_,0,0,0,m12_]:>-(1/(2 eIR^2 m12))+(-(3/(2 m12))-Log[\[Mu]^2/m12]/(2 m12))/eIR+C0iFin[cc11,0,m12,0,0,0,m12]/;zeroChecks[{m12}], 
C0i[cc12,0,m12_,0,0,0,m12_]:>C0iFin[cc12,0,m12,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc22,0,m12_,0,0,0,m12_]:>C0iFin[cc22,0,m12,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc001,0,m12_,0,0,0,m12_]:>-(1/(12 eUV))+C0iFin[cc001,0,m12,0,0,0,m12]/;zeroChecks[{m12}], 
C0i[cc002,0,m12_,0,0,0,m12_]:>-(1/(12 eUV))+C0iFin[cc002,0,m12,0,0,0,m12]/;zeroChecks[{m12}],
C0i[cc112,0,m12_,0,0,0,m12_]:>C0iFin[cc112,0,m12,0,0,0,m12]/;zeroChecks[{m12}],
(*C0i[cc122,0,m12_,0,0,0,m12_] (*Covered by c112 (differs by a factor of 4 )*)*)



C0i[cc0,0,m12_,m12_,0,0,m12_]:>-(1/(2 eIR m12))+C0iFin[cc0,0,m12,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc00,0,m12_,m12_,0,0,m12_]:>1/(4 eUV)+C0iFin[cc00,0,m12,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc22,0,m12_,m12_,0,0,m12_]:>C0iFin[cc22,0,m12,m12,0,0,m12]/;zeroChecks[{m12}],
C0i[cc002,0,m12_,m12_,0,0,m12_]:>-(1/(12 eUV))+C0iFin[cc002,0,m12,m12,0,0,m12]/;zeroChecks[{m12}],

C0i[cc0,m12_,0,m12_,0,m12_,m12_]:>1/(2 eIR m12)+C0iFin[cc0,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc00,m12_,0,m12_,0,m12_,m12_]:>1/(4 eUV)+C0iFin[cc00,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc1,m12_,0,m12_,0,m12_,m12_]:>C0iFin[cc1,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc2,m12_,0,m12_,0,m12_,m12_]:>C0iFin[cc2,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc11,m12_,0,m12_,0,m12_,m12_]:>C0iFin[cc11,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc12,m12_,0,m12_,0,m12_,m12_]:>C0iFin[cc12,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],
C0i[cc12,m12_,0,m12_,0,m12_,m12_]:>C0iFin[cc22,m12,0,m12,0,m12,m12]/;zeroChecks[{m12}],


(* Two scales *)
C0i[cc0,m12_,0,m22_,0,0,0]:>(Log[-(\[Mu]^2/m12)]/(m12-m22)-Log[-(\[Mu]^2/m22)]/(m12-m22))/eIR+C0iFin[cc0,m12,0,m22,0,0,0]/;zeroChecks[{m12,m22}],


(*C0i[cc0,0,m12_,m22_,0,0,0]:>+C0iFin[cc0,0,m12,m22,0,0,0]/;zeroChecks[{m12,m22}], covered by cc0:102000 above*)
C0i[cc2,0,m12_,m22_,0,0,0]:>C0iFin[cc2,0,m12,m22,0,0,0]/;zeroChecks[{m12,m22}],
C0i[cc00,0,m12_,m22_,0,0,0]:>1/(4 eUV)+C0iFin[cc00,0,m12,m22,0,0,0]/;zeroChecks[{m12,m22}],
C0i[cc12,0,m12_,m22_,0,0,0]:>C0iFin[cc12,0,m12,m22,0,0,0]/;zeroChecks[{m12,m22}],
C0i[cc22,0,m12_,m22_,0,0,0]:>C0iFin[cc22,0,m12,m22,0,0,0]/;zeroChecks[{m12,m22}],

C0i[cc0,0,m12_,0,m22_,0,0]:>C0iFin[cc0,0,m12,0,m22,0,0]/;zeroChecks[{m12,m22}],


C0i[cc0,m12_,0,0,0,0,m22_]:>C0iFin[cc0,m12,0,0,0,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc00,m12_,0,0,0,0,m22_]:>1/(4 eUV)+C0iFin[cc00,m12,0,0,0,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc1,m12_,0,0,0,0,m22_]:>C0iFin[cc1,m12,0,0,0,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc2,m12_,0,0,0,0,m22_]:>C0iFin[cc2,m12,0,0,0,0,m22]/;zeroChecks[{m12,m22}], (* Double checked *)

C0i[cc0,0,m12_,0,0,0,m22_]:>Log[m22/(-m12+m22)]/(eIR m12)+C0iFin[cc0,0,m12,0,0,0,m22]/;zeroChecks[{m12,m22}], 
C0i[cc1,0,m12_,0,0,0,m22_]:>(1/m12-(m22 Log[m22/(-m12+m22)])/m12^2)/eIR+C0iFin[cc1,0,m12,0,0,0,m22]/;zeroChecks[{m12,m22}], 
C0i[cc2,0,m12_,0,0,0,m22_]:>C0iFin[cc2,0,m12,0,0,0,m22]/;zeroChecks[{m12,m22}], 
C0i[cc00,0,m12_,0,0,0,m22_]:>1/(4 eUV)+C0iFin[cc00,0,m12,0,0,0,m22]/;zeroChecks[{m12,m22}], 

C0i[cc0,0,0,0,0,m12_,m22_]:>C0iFin[cc0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc00,0,0,0,0,m12_,m22_]:>1/(4 eUV)+C0iFin[cc00,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}], 

C0i[cc0,m12_,0,0,m22_,m22_,0]:>C0iFin[cc0,m12,0,0,m22,m22,0]/;zeroChecks[{m12,m22}],

C0i[cc0,0,m12_,0,0,m12_,m22_]:>C0iFin[cc0,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc1,0,m12_,0,0,m12_,m22_]:>C0iFin[cc1,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc2,0,m12_,0,0,m12_,m22_]:>C0iFin[cc2,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc00,0,m12_,0,0,m12_,m22_]:>1/(4 eUV)+C0iFin[cc00,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], (* Double checked *)
C0i[cc11,0,m12_,0,0,m12_,m22_]:>C0iFin[cc11,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc12,0,m12_,0,0,m12_,m22_]:>C0iFin[cc12,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}],
C0i[cc22,0,m12_,0,0,m12_,m22_]:>C0iFin[cc22,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc001,0,m12_,0,0,m12_,m22_]:>-(1/(12 eUV))+C0iFin[cc001,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc002,0,m12_,0,0,m12_,m22_]:>-(1/(12 eUV))+C0iFin[cc002,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc112,0,m12_,0,0,m12_,m22_]:>C0iFin[cc112,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 
C0i[cc122,0,m12_,0,0,m12_,m22_]:>C0iFin[cc122,0,m12,0,0,m12,m22]/;zeroChecks[{m12,m22}], 


C0i[cc00,0,m12_,m12_,0,0,m22_]:>1/(4 eUV)+C0iFin[cc00,0,m12,m12,0,0,m22]/;zeroChecks[{m12,m22}],

C0i[cc0,0,m12_,0,0,m22_,m22_]:>C0iFin[cc0,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc1,0,m12_,0,0,m22_,m22_]:>C0iFin[cc1,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc2,0,m12_,0,0,m22_,m22_]:>C0iFin[cc2,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc00,0,m12_,0,0,m22_,m22_]:> 1/(4 eUV)+C0iFin[cc00,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}],  
C0i[cc001,0,m12_,0,0,m22_,m22_]:>-(1/(12 eUV))+C0iFin[cc001,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], 
(*C0i[cc002,0,m12_,0,0,m22_,m22_]:>+C0iFin[cc002,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], (covered by cc001)*)
C0i[cc12,0,m12_,0,0,m22_,m22_]:>C0iFin[cc12,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], 
C0i[cc112,0,m12_,0,0,m22_,m22_]:>C0iFin[cc112,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], 
C0i[cc122,0,m12_,0,0,m22_,m22_]:>C0iFin[cc122,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], 
C0i[cc22,0,m12_,0,0,m22_,m22_]:>C0iFin[cc22,0,m12,0,0,m22,m22]/;zeroChecks[{m12,m22}], 

C0i[cc0,0,m12_,0,0,m22_,m12_]:>C0iFin[cc0,0,m12,0,0,m22,m12]/;zeroChecks[{m12,m22}],
C0i[cc1,0,m12_,0,0,m22_,m12_]:>C0iFin[cc1,0,m12,0,0,m22,m12]/;zeroChecks[{m12,m22}],
C0i[cc2,0,m12_,0,0,m22_,m12_]:>C0iFin[cc2,0,m12,0,0,m22,m12]/;zeroChecks[{m12,m22}],

C0i[cc0,0,0,m12_,m22_,0,m22_]:>C0iFin[cc0,0,0,m12,m22,0,m22]/;zeroChecks[{m12,m22}],

C0i[cc0,0,m12_,m12_,0,0,m22_]:>-(1/(eIR (m12-m22)))+C0iFin[cc0,0,m12,m12,0,0,m22]/;zeroChecks[{m12,m22}],
C0i[cc22,0,m12_,m12_,0,0,m22_]:>C0iFin[cc22,0,m12,m12,0,0,m22]/;zeroChecks[{m12,m22}],
C0i[cc002,0,m12_,m12_,0,0,m22_]:>-(5/36)-m22/(6 m12)+m22^2/(6 m12^2)-1/12 Log[m22/(-m12+m22)]+(m22^2 Log[m22/(-m12+m22)])/(4 m12^2)-(m22^3 Log[m22/(-m12+m22)])/(6 m12^3)-1/12 Log[\[Mu]^2/m22]+C0iFin[cc002,0,m12,m12,0,0,m22]/;zeroChecks[{m12,m22}],

C0i[cc00,m12_,0,m12_,0,m22_,m22_]:>1/(4 eUV)+C0iFin[cc00,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc1,m12_,0,m12_,0,m22_,m22_]:>C0iFin[cc1,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc2,m12_,0,m12_,0,m22_,m22_]:>C0iFin[cc2,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc11,m12_,0,m12_,0,m22_,m22_]:>C0iFin[cc11,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc12,m12_,0,m12_,0,m22_,m22_]:>C0iFin[cc12,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],
C0i[cc22,m12_,0,m12_,0,m22_,m22_]:>C0iFin[cc22,m12,0,m12,0,m22,m22]/;zeroChecks[{m12,m22}],

C0i[cc0,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc0,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc00,m12_,0,m12_,m22_,m12_,m12_]:>1/(4 eUV)+C0iFin[cc00,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc1,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc1,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc2,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc2,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc11,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc11,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc12,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc12,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],
C0i[cc22,m12_,0,m12_,m22_,m12_,m12_]:>C0iFin[cc22,m12,0,m12,m22,m12,m12]/;zeroChecks[{m12,m22}],

(* Three scales *)
C0i[cc0,m12_,0,0,m22_,m22_,m32_]:>C0iFin[cc0,m12,0,0,m22,m22,m32]/;zeroChecks[{m12,m22,m32}],



(***********************************)
(* D0i integrals - Divergences only *)
(***********************************)
(* WARNING: PACKAGE-X GIVES SOME WRONG RESULTS FOR THIS - use the explicit formula  *)
(***********************************)
(* Scaleless *)

(* One scale *)
D0i[dd0,0,0,0,0,0,0,0,m12_,0,0]:>1/(eIR m12^2)+D0iFin[dd0,0,0,0,0,0,0,0,m12,0,0]/;zeroChecks[{m12}],
D0i[dd00,0,0,0,0,0,0,0,m12_,0,0]:>1/(4 eIR m12)+D0iFin[dd00,0,0,0,0,0,0,0,m12,0,0]/;zeroChecks[{m12}],

D0i[dd0,0,0,0,0,0,0,0,0,0,m12_]:>1/(eIR m12^2)+D0iFin[dd0,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
D0i[dd1,0,0,0,0,0,0,0,0,0,m12_]:>-(1/(2 eIR m12^2))+D0iFin[dd1,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
D0i[dd00,0,0,0,0,0,0,0,0,0,m12_]:>1/(4 eIR m12)+D0iFin[dd00,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
D0i[dd11,0,0,0,0,0,0,0,0,0,m12_]:>1/(3 eIR m12^2)+D0iFin[dd11,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
(*D0i[dd12,0,0,0,0,0,0,0,0,0,m12_]:>1/(6 eIR m12^2)+D0iFin[dd12,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],*) (* covered by d11*)
D0i[dd13,0,0,0,0,0,0,0,0,0,m12_]:>-(1/(6 eIR m12^2))+D0iFin[dd13,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],
(*D0i[dd23,0,0,0,0,0,0,0,0,0,m12_]:>1/(6 eIR m12^2)+D0iFin[dd23,0,0,0,0,0,0,0,0,0,m12]/;zeroChecks[{m12}],*) (* Covered by dd13*)



(* Two scales *)
D0i[dd0,0,0,0,0,m12_,m22_,0,0,0,0]:>4/(eIR^2 m12 m22)+((2 Log[-(\[Mu]^2/m12)])/(m12 m22)+(2 Log[-(\[Mu]^2/m22)])/(m12 m22))/eIR+D0iFin[dd0,0,0,0,0,m12,m22,0,0,0,0]/;zeroChecks[{m12,m22}],


D0i[dd0,0,0,0,0,0,0,0,0,m12_,m22_]:>-(1/(eIR m12 m22))+D0iFin[dd0,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd1,0,0,0,0,0,0,0,0,m12_,m22_]:>1/(2 eIR m12 m22)+D0iFin[dd1,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd2,0,0,0,0,0,0,0,0,m12_,m22_]:>D0iFin[dd2,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd00,0,0,0,0,0,0,0,0,m12_,m22_]:>D0iFin[dd00,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd11,0,0,0,0,0,0,0,0,m12_,m22_]:>-(1/(3 eIR m12 m22))+D0iFin[dd11,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd12,0,0,0,0,0,0,0,0,m12_,m22_]:>D0iFin[dd12,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd13,0,0,0,0,0,0,0,0,m12_,m22_]:>D0iFin[dd13,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],
D0i[dd23,0,0,0,0,0,0,0,0,m12_,m22_]:>D0iFin[dd23,0,0,0,0,0,0,0,0,m12,m22]/;zeroChecks[{m12,m22}],



(* Three scales *) (* I have no way to check these at present... I have to trust package X *)
D0i[dd0,0,0,0,m12_,m22_,m32_,0,0,0,0]:>2/(eIR^2 m22 m32)+(-((2 Log[-(\[Mu]^2/m12)])/(m22 m32))+(2 Log[-(\[Mu]^2/m22)])/(m22 m32)+(2 Log[-(\[Mu]^2/m32)])/(m22 m32))/eIR+D0iFin[dd0,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd2,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(1/(eIR^2 m22 m32))+((m12 Log[-(\[Mu]^2/m12)])/((m12-m22) m22 m32)-(m12 Log[-(\[Mu]^2/m22)])/((m12-m22) m22 m32)-Log[-(\[Mu]^2/m32)]/(m22 m32))/eIR+D0iFin[dd2,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd3,0,0,0,m12_,m22_,m32_,0,0,0,0]:>(-(Log[-(\[Mu]^2/m12)]/((m12-m22) m32))+Log[-(\[Mu]^2/m22)]/((m12-m22) m32))/eIR+D0iFin[dd3,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd00,0,0,0,m12_,m22_,m32_,0,0,0,0]:>D0iFin[dd00,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd12,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(1/(eIR m22 m32))+D0iFin[dd12,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd13,0,0,0,m12_,m22_,m32_,0,0,0,0]:>D0iFin[dd13,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd22,0,0,0,m12_,m22_,m32_,0,0,0,0]:>1/(eIR^2 m22 m32)+((m12-2 m22)/((m12-m22) m22 m32)-(m12^2 Log[-(\[Mu]^2/m12)])/((m12-m22)^2 m22 m32)+(m12^2 Log[-(\[Mu]^2/m22)])/((m12-m22)^2 m22 m32)+Log[-(\[Mu]^2/m32)]/(m22 m32))/eIR+D0iFin[dd22,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd23,0,0,0,m12_,m22_,m32_,0,0,0,0]:>(1/((m12-m22) m32)+(m12 Log[-(\[Mu]^2/m12)])/((m12-m22)^2 m32)-(m12 Log[-(\[Mu]^2/m22)])/((m12-m22)^2 m32))/eIR+D0iFin[dd23,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}],
D0i[dd33,0,0,0,m12_,m22_,m32_,0,0,0,0]:>(-(1/((m12-m22) m32))-(m22 Log[-(\[Mu]^2/m12)])/((-m12+m22)^2 m32)+(m22 Log[-(\[Mu]^2/m22)])/((-m12+m22)^2 m32))/eIR+D0iFin[dd33,0,0,0,m12,m22,m32,0,0,0,0]/;zeroChecks[{m12,m22,m32}]
};


intFinReps = {
(* A0Fin integral *)
A0Fin[m12_] :> m12+m12 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],

(********************)
(* B0iFin integrals *)
(********************)
(* One scale *)

B0iFin[bb0,m12_,0,0]:>2+Log[-(\[Mu]^2/m12)]/;zeroChecks[{m12}],
B0iFin[bb1,m12_,0,0]:>-1+1/2 (-Log[-(\[Mu]^2/m12)])/;zeroChecks[{m12}], (* Double checked *)
B0iFin[bb00,m12_,0,0]:>-((2 m12)/9)-1/12 m12 (Log[-(\[Mu]^2/m12)])/;zeroChecks[{m12}],
B0iFin[bb11,m12_,0,0]:>13/18+1/3 Log[-(\[Mu]^2/m12)]/;zeroChecks[{m12}],
B0iFin[dbb0,m12_,0,0]:>-(1/m12)/;zeroChecks[{m12}],
B0iFin[dbb1,m12_,0,0]:>(1/(2 m12))/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb00,m12_,0,0]:>-(5/36)+1/12 (-Log[-(\[Mu]^2/m12)])/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb11,m12_,0,0]:>-1/(3 m12)/;zeroChecks[{m12}],

B0iFin[bb0,0,0,m12_]:>1+Log[\[Mu]^2/m12]/;zeroChecks[{m12}], (* Double checked *)
B0iFin[bb1,0,0,m12_]:>-(1/4)+1/2 (-Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
B0iFin[bb00,0,0,m12_]:>1/8 m12 (3+2 Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
B0iFin[dbb0,0,0,m12_]:>1/(2 m12)/;zeroChecks[{m12}],
B0iFin[dbb00,0,0,m12_]:>1/72 (-5-6Log[\[Mu]^2/m12])/;zeroChecks[{m12}],

B0iFin[bb1,m12_,m12_,0]:>-(3/2)+1/2 (-Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
B0iFin[bb00,m12_,m12_,0]:>(5 m12)/18+1/6 m12 (Log[\[Mu]^2/m12])/;zeroChecks[{m12}],


B0iFin[bb0,m12_,0,m12_]:> 2+Log[\[Mu]^2/m12]/;zeroChecks[{m12}], (* Double checked *)
B0iFin[bb1,m12_,0,m12_]:>-(1/2)-1/2 Log[\[Mu]^2/m12]/;zeroChecks[{m12}], (* Double checked *)
B0iFin[bb00,m12_,0,m12_]:>(5 m12)/18+1/6 m12 (Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
B0iFin[bb11,m12_,0,m12_]:> 2/9+1/3 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],
B0iFin[dbb0,m12_,0,m12_]:>-(1/m12)-Log[\[Mu]^2/m12]/(2 m12)/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb1,m12_,0,m12_]:>-(1/(2 m12))/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb00,m12_,0,m12_]:>-(5/36)+1/12 (-Log[\[Mu]^2/m12])/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb11,m12_,0,m12_]:>1/(6 m12)/;zeroChecks[{m12}],


B0iFin[bb0,0,m12_,m12_]:>Log[\[Mu]^2/m12]/;zeroChecks[{m12}], (* Double checked *)
B0iFin[bb1,0,m12_,m12_]:>1/2 (-Log[\[Mu]^2/m12])/;zeroChecks[{m12}],  (* Double checked *)
B0iFin[bb00,0,m12_,m12_]:>m12/2 (1+Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
B0iFin[dbb0,0,m12_,m12_]:>1/(6m12)/;zeroChecks[{m12}], (* Double checked *)
B0iFin[dbb00,0,m12_,m12_]:>-(1/12) (Log[\[Mu]^2/m12])/;zeroChecks[{m12}], (* Double checked *)

(* Two scales *)

B0iFin[bb1,m12_,m22_,0]:>-((2 m12+m22)/(2 m12))-((m12^2-m22^2) Log[m22/(-m12+m22)])/(2 m12^2)+1/2 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb00,m12_,m22_,0]:>-((8 m12^2-21 m12 m22+3 m22^2)/(36 m12))-((m12-m22)^3 Log[m22/(-m12+m22)])/(12 m12^2)+1/12 (-m12+3 m22) (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],

B0iFin[bb0,m12_,0,m22_]:>2+((m12-m22) Log[m22/(-m12+m22)])/m12+Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[bb1,m12_,0,m22_]:>-((2 m12-m22)/(2 m12))-((m12-m22)^2 Log[m22/(-m12+m22)])/(2 m12^2)+1/2 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[bb00,m12_,0,m22_]:>-((8 m12^2-21 m12 m22+3 m22^2)/(36 m12))-((m12-m22)^3 Log[m22/(-m12+m22)])/(12 m12^2)+1/12 (-m12+3 m22) (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}], 
B0iFin[bb11,m12_,0,m22_]:>(13 m12^2-15 m12 m22+6 m22^2)/(18 m12^2)+((m12-m22)^3 Log[m22/(-m12+m22)])/(3 m12^3)+1/3 (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[dbb0,m12_,0,m22_]:>-(1/m12)+(m22 Log[m22/(-m12+m22)])/m12^2/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb1,m12_,0,m22_]:>((m12-2 m22)/(2 m12^2)-((m12-m22) m22 Log[m22/(-m12+m22)])/m12^3)/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb00,m12_,0,m22_]:>-((5 m12^2+6 m12 m22-6 m22^2)/(36 m12^2))-((m12-m22)^2 (m12+2 m22) Log[m22/(-m12+m22)])/(12 m12^3)+1/12 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb11,m12_,0,m22_]:> (-((2 m12^2-9 m12 m22+6 m22^2)/(6 m12^3))+((m12-m22)^2 m22 Log[m22/(-m12+m22)])/m12^4)/;zeroChecks[{m12,m22}],

B0iFin[bb0,0,m12_,m22_]:>1-(m12 Log[m12/m22])/(m12-m22)+Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],
B0iFin[bb1,0,m12_,m22_]:>-((3 m12-m22)/(4 (m12-m22)))+(m12^2 Log[m12/m22])/(2 (m12-m22)^2)+1/2 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb00,0,m12_,m22_]:>(-2 m12^2 Log[m12/m22]+(m12^2-m22^2) (3+2 Log[\[Mu]^2/m22]))/(8 (m12-m22))/;zeroChecks[{m12,m22}],
B0iFin[dbb0,0,m12_,m22_]:>(m12^2-m22^2-2 m12 m22 Log[m12/m22])/(2 (m12-m22)^3)/;zeroChecks[{m12,m22}],
B0iFin[dbb00,0,m12_,m22_]:>(-5 m12^2+22 m12 m22-5 m22^2)/(72 (m12-m22)^2)-(m12^2 (m12-3 m22) Log[\[Mu]^2/m12])/(12 (m12-m22)^3)+(m22^2 (-3 m12+m22) Log[\[Mu]^2/m22])/(12 (m12-m22)^3)/;zeroChecks[{m12,m22}],

B0iFin[bb0,m12_,m22_,m12_]:>2+DiscB[m12,Sqrt[m12],Sqrt[m22]]+(m22 Log[m12/m22])/(2 m12)+Log[\[Mu]^2/m12]/;zeroChecks[{m12,m22}],
B0iFin[bb1,m12_,m22_,m12_]:>-((m12+m22)/(2 m12))-(m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12)+((2 m12-m22) m22 Log[m12/m22])/(4 m12^2)+1/2 (-Log[\[Mu]^2/m12])/;zeroChecks[{m12,m22}],
B0iFin[bb00,m12_,m22_,m12_]:>(10 m12^2+27 m12 m22-3 m22^2)/(36 m12)+((4 m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12)+((6 m12-m22) m22^2 Log[m12/m22])/(24 m12^2)+1/12 (2 m12+3 m22) (Log[\[Mu]^2/m12])/;zeroChecks[{m12,m22}],
B0iFin[bb11,m12_,m22_,m12_]:> (4 m12^2-9 m12 m22+6 m22^2)/(18 m12^2)-((m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(3 m12^2)-((3 m12-m22) m22^2 Log[m12/m22])/(6 m12^3)+1/3 (Log[\[Mu]^2/m12])/;zeroChecks[{m12,m22}],
B0iFin[dbb0,m12_,m22_,m12_]:>-(1/m12)-((3 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12 (4 m12-m22))+((m12-m22) Log[m12/m22])/(2 m12^2)/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb1,m12_,m22_,m12_]:>(-((m12-2 m22)/(2 m12^2))-((2 m12^2-4 m12 m22+m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12^2 (4 m12-m22))-((2 m12-m22) m22 Log[m12/m22])/(2 m12^3))/;zeroChecks[{m12,m22}],
B0iFin[dbb00,m12_,m22_,m12_]:>(-((5 m12^2+18 m12 m22-6 m22^2)/(36 m12^2))-((5 m12-2 m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12^2)+(m22 (6 m12^2-9 m12 m22+2 m22^2) Log[m12/m22])/(24 m12^3)+1/12 (-Log[\[Mu]^2/m12])) /;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb11,m12_,m22_,m12_]:>((m12^2+9 m12 m22-6 m22^2)/(6 m12^3)+(m22 (5 m12^2-5 m12 m22+m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12^3 (4 m12-m22))-(m22 (m12^2-3 m12 m22+m22^2) Log[m12/m22])/(2 m12^4)) /;zeroChecks[{m12,m22}],


B0iFin[bb0,m12_,m12_,m22_]:>2+DiscB[m12,Sqrt[m12],Sqrt[m22]]-((2 m12-m22) Log[m12/m22])/(2 m12)+Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[bb1,m12_,m12_,m22_]:>-((3 m12-m22)/(2 m12))-((2 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12)+((2 m12^2-4 m12 m22+m22^2) Log[m12/m22])/(4 m12^2)+1/2 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[bb00,m12_,m12_,m22_]:>(10 m12^2+27 m12 m22-3 m22^2)/(36 m12)+((4 m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12)-((4 m12^3+6 m12^2 m22-6 m12 m22^2+m22^3) Log[m12/m22])/(24 m12^2)+1/12 (2 m12+3 m22) (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb11,m12_,m12_,m22_]:> (22 m12^2-27 m12 m22+6 m22^2)/(18 m12^2)+((3 m12^2-4 m12 m22+m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(3 m12^2)-((2 m12^3-9 m12^2 m22+6 m12 m22^2-m22^3) Log[m12/m22])/(6 m12^3)+1/3 (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb001,m12_,m12_,m22_]:> -(1/(144 m12^3))(6 m12 m22 (8 m12^2-6 m12 m22+m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]]-3 (2 m12^4+8 m12^3 m22-18 m12^2 m22^2+8 m12 m22^3-m22^4) Log[m12/m22]+m12 (13 m12^3+88 m12^2 m22-39 m12 m22^2+6 m22^3+6 m12^2 (m12+4 m22) Log[\[Mu]^2/m22]))/;zeroChecks[{m12,m22}],
B0iFin[dbb0,m12_,m12_,m22_]:>-(1/m12)-((3 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12 (4 m12-m22))+((m12-m22) Log[m12/m22])/(2 m12^2)/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb1,m12_,m12_,m22_]:>(3 m12-2 m22)/(2 m12^2)+((5 m12^2-5 m12 m22+m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12^2 (4 m12-m22))-((m12^2-3 m12 m22+m22^2) Log[m12/m22])/(2 m12^3)/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb00,m12_,m12_,m22_]:>-((5 m12^2+18 m12 m22-6 m22^2)/(36 m12^2))-((5 m12-2 m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12^2)+((2 m12^3+6 m12^2 m22-9 m12 m22^2+2 m22^3) Log[m12/m22])/(24 m12^3)+1/12 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}], (* Double checked *)
B0iFin[dbb11,m12_,m12_,m22_]:>-((11 m12^2-21 m12 m22+6 m22^2)/(6 m12^3))-((7 m12^3-14 m12^2 m22+7 m12 m22^2-m22^3) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(m12^3 (4 m12-m22))+((m12^3-6 m12^2 m22+5 m12 m22^2-m22^3) Log[m12/m22])/(2 m12^4) /;zeroChecks[{m12,m22}],

B0iFin[bb0,m12_,m22_,m22_]:> 2+DiscB[m12,Sqrt[m22],Sqrt[m22]]+Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],
B0iFin[bb1,m12_,m22_,m22_]:> -1-1/2 DiscB[m12,Sqrt[m22],Sqrt[m22]]+1/2 (-Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb00,m12_,m22_,m22_]:>1/18 (-4 m12+21 m22)+1/12 (-m12+4 m22) DiscB[m12,Sqrt[m22],Sqrt[m22]]+1/12 (-m12+6 m22) (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[bb11,m12_,m22_,m22_]:>(13 m12-12 m22)/(18 m12)+((m12-m22) DiscB[m12,Sqrt[m22],Sqrt[m22]])/(3 m12)+1/3 (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
B0iFin[dbb0,m12_,m22_,m22_]:> -(1/m12)-(2 m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(m12 (-m12+4 m22))/;zeroChecks[{m12,m22}],
B0iFin[dbb1,m12_,m22_,m22_]:> 1/(2 m12)+(m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(m12 (-m12+4 m22)) /;zeroChecks[{m12,m22}],
B0iFin[dbb00,m12_,m22_,m22_]:> (-((5 m12+12 m22)/(36 m12))-((m12+2 m22) DiscB[m12,Sqrt[m22],Sqrt[m22]])/(12 m12)+1/12 (-Log[\[Mu]^2/m22]))/;zeroChecks[{m12,m22}],
B0iFin[dbb11,m12_,m22_,m22_]:> (-((m12-3 m22)/(3 m12^2))+((m12-2 m22) m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(m12^2 (m12-4 m22)))/;zeroChecks[{m12,m22}],


(* Three scales *)
B0iFin[bb0,m12_,m22_,m32_]:>2+DiscB[m12,Sqrt[m22],Sqrt[m32]]-((m12+m22-m32) Log[m22/m32])/(2 m12)+Log[\[Mu]^2/m32] /;zeroChecks[{m12,m22,m32}],
B0iFin[bb1,m12_,m22_,m32_]:>-((2 m12+m22-m32)/(2 m12))-((m12+m22-m32) DiscB[m12,Sqrt[m22],Sqrt[m32]])/(2 m12)+((m12^2+m22^2-2 m12 m32-2 m22 m32+m32^2) Log[m22/m32])/(4 m12^2)+1/2 (-Log[\[Mu]^2/m32])/;zeroChecks[{m12,m22,m32}],
B0iFin[bb00,m12_,m22_,m32_]:>-((8 m12^2-21 m12 m22+3 m22^2-21 m12 m32-6 m22 m32+3 m32^2)/(36 m12))-((m12^2-2 m12 m22+m22^2-2 m12 m32-2 m22 m32+m32^2) DiscB[m12,Sqrt[m22],Sqrt[m32]])/(12 m12)+((m12^3-3 m12^2 m22-3 m12 m22^2+m22^3-3 m12^2 m32-3 m22^2 m32+3 m12 m32^2+3 m22 m32^2-m32^3) Log[m22/m32])/(24 m12^2)+1/12 (-m12+3 m22+3 m32) (Log[\[Mu]^2/m32])/;zeroChecks[{m12,m22,m32}],
B0iFin[bb001,m12_,m22_,m32_]:>1/(144 m12^3) (6 m12 (m12^3+(m22-m32)^3-m12^2 (m22+3 m32)-m12 (m22^2+2 m22 m32-3 m32^2)) DiscB[m12,Sqrt[m22],Sqrt[m32]]-3 (m12^4+(m22-m32)^4+6 m12^2 m32^2-2 m12^3 (m22+2 m32)-2 m12 (m22-m32)^2 (m22+2 m32)) Log[m22/m32]+m12 (16 m12^3+6 (m22-m32)^3-2 m12^2 (13 m22+29 m32)-3 m12 (3 m22^2+4 m22 m32-7 m32^2)+6 m12^2 (m12-2 (m22+2 m32)) Log[\[Mu]^2/m32]))/;zeroChecks[{m12,m22,m32}],

B0iFin[bb11,m12_,m22_,m32_]:>(13 m12^2+3 m12 m22+6 m22^2-15 m12 m32-12 m22 m32+6 m32^2)/(18 m12^2)+((m12^2+m12 m22+m22^2-2 m12 m32-2 m22 m32+m32^2) DiscB[m12,Sqrt[m22],Sqrt[m32]])/(3 m12^2)-((m12^3+m22^3-3 m12^2 m32-3 m12 m22 m32-3 m22^2 m32+3 m12 m32^2+3 m22 m32^2-m32^3) Log[m22/m32])/(6 m12^3)+1/3 (Log[\[Mu]^2/m32])/;zeroChecks[{m12,m22,m32}],
B0iFin[dbb0,m12_,m22_,m32_]:>-(1/m12)+(m12 (-(m22-m32)^2+m12 (m22+m32)) DiscB[m12,Sqrt[m22],Sqrt[m32]])/(m12^2 (m12^2+(m22-m32)^2-2 m12 (m22+m32)))+1/2 (m22-m32)/m12^2 Log[m22/m32]/;zeroChecks[{m12,m22,m32}],
B0iFin[dbb00,m12_,m22_,m32_]:>-(1/(72 m12^3))(10 m12^3-12 m12 (m22-m32)^2+12 m12^2 (m22+m32)+6 m12 (m12^2-2 (m22-m32)^2+m12 (m22+m32)) DiscB[m12,Sqrt[m22],Sqrt[m32]]-3 (m12^3-2 (m22-m32)^3+3 m12 (m22^2-m32^2)) Log[m22/m32]+6 m12^3 Log[\[Mu]^2/m32])/;zeroChecks[{m12,m22,m32}],


(********************)
(* C0iFin integrals *)
(********************)
(* One scale *)
C0iFin[cc0,m12_,0,0,0,0,0]:>-(\[Pi]^2/(12 m12))+Log[-(\[Mu]^2/m12)]^2/(2 m12)/;zeroChecks[{m12}],

C0iFin[cc0,0,m12_,0,0,0,0]:>-(\[Pi]^2/(12 m12))+Log[-(\[Mu]^2/m12)]^2/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc1,0,m12_,0,0,0,0]:>2/m12+Log[-(\[Mu]^2/m12)]/m12/;zeroChecks[{m12}],
(*C0iFin[cc2,0,m12_,0,0,0,0]:>/;zeroChecks[{m12}], covered by cc1*)
C0iFin[cc00,0,m12_,0,0,0,0]:>3/4+1/4 Log[-(\[Mu]^2/m12)]/;zeroChecks[{m12}],
C0iFin[cc11,0,m12_,0,0,0,0]:>-(1/m12)-Log[-(\[Mu]^2/m12)]/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc12,0,m12_,0,0,0,0]:>1/(2 m12)/;zeroChecks[{m12}],

C0iFin[cc0,0,0,0,0,0,m12_]:>1/m12+Log[\[Mu]^2/m12]/m12/;zeroChecks[{m12}],
C0iFin[cc00,0,0,0,0,0,m12_]:>3/8+1/4 (Log[\[Mu]^2/m12])/;zeroChecks[{m12}],

C0iFin[cc0,0,0,m12_,0,0,0]:>-(\[Pi]^2/(12 m12))+Log[-(\[Mu]^2/m12)]^2/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc1,0,0,m12_,0,0,0]:>-(4/m12)+\[Pi]^2/(12 m12)-(2 Log[-(\[Mu]^2/m12)])/m12-Log[-(\[Mu]^2/m12)]^2/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc2,0,0,m12_,0,0,0]:>2/m12+Log[-(\[Mu]^2/m12)]/m12/;zeroChecks[{m12}],
C0iFin[cc00,0,0,m12_,0,0,0]:>3/4+1/4 Log[-(\[Mu]^2/m12)]/;zeroChecks[{m12}],

C0iFin[cc0,m12_,0,0,0,0,m12_]:>-(\[Pi]^2/(12 m12))-(I \[Pi] Log[2])/m12 tagIM/;zeroChecks[{m12}],
C0iFin[cc00,m12_,0,0,0,0,m12_]:>1/12 (15+9 I \[Pi] tagIM-\[Pi]^2)-I tagIM \[Pi] Log[2]+1/4 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],
C0iFin[cc1,m12_,0,0,0,0,m12_]:>(12+12 tagIM I \[Pi]-\[Pi]^2)/(12 m12)-(I tagIM \[Pi] Log[2])/m12/;zeroChecks[{m12}],
C0iFin[cc2,m12_,0,0,0,0,m12_]:>(-8+\[Pi]^2-8 I \[Pi] tagIM)/(4 m12)+(3 I tagIM \[Pi] Log[2])/m12/;zeroChecks[{m12}],

C0iFin[cc0,0,0,m12_,0,0,m12_]:>-(\[Pi]^2/(24 m12))-Log[\[Mu]^2/m12]^2/(4 m12)/; zeroChecks[{m12}],
C0iFin[cc1,0,0,m12_,0,0,m12_]:>-(3/m12)-Log[\[Mu]^2/m12]/m12/; zeroChecks[{m12}],
C0iFin[cc2,0,0,m12_,0,0,m12_]:>1/m12/; zeroChecks[{m12}],
C0iFin[cc00,0,0,m12_,0,0,m12_]:>1/2+1/4 Log[\[Mu]^2/m12]/; zeroChecks[{m12}],
C0iFin[cc12,0,0,m12_,0,0,m12_]:>-(1/(4 m12))/; zeroChecks[{m12}],
(*C0iFin[cc22,0,0,m12_,0,0,m12_]:>/; zeroChecks[{m12}],*) (* covered by c12 *)
C0iFin[cc001,0,0,m12_,0,0,m12_]:>-(13/72)-1/12 Log[\[Mu]^2/m12]/; zeroChecks[{m12}],
C0iFin[cc002,0,0,m12_,0,0,m12_]:>-(7/72)-1/12 Log[\[Mu]^2/m12]/; zeroChecks[{m12}],
C0iFin[cc112,0,0,m12_,0,0,m12_]:>1/(9 m12)/; zeroChecks[{m12}],
(*C0iFin[cc122,0,0,m12_,0,0,m12_]:>1/(18 m12)/; zeroChecks[{m12}],*) (* covered by 112 *)
(*C0iFin[cc222,0,0,m12_,0,0,m12_]:>1/(9 m12)/; zeroChecks[{m12}],*)  (* covered by 112 *)

C0iFin[cc0,0,0,0,0,m12_,m12_]:>-1/m12/;zeroChecks[{m12}],
C0iFin[cc00,0,0,0,0,m12_,m12_]:>1/8+1/4 (Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
C0iFin[cc1,0,0,0,0,m12_,m12_]:>1/(4m12)/;zeroChecks[{m12}],
(*C0iFin[cc2,0,0,0,0,m12_,m12_]:1/(4m12)/;zeroChecks[{m12}], (* covered by cc1 *)*)

(*C0iFin[cc0,0,0,m12_,0,0,m12_] SAME AS C0iFin[cc0,0,m12_,0,0,0,m12_]*)

C0iFin[cc1,m12_,0,m12_,0,0,0]:>1/(2 m12)+Log[-(\[Mu]^2/m12)]/(2 m12)/;zeroChecks[{m12}],
(*C0iFin[cc2,m12,0,m12,0,0,0] (*Covered by cc1*)*)

C0iFin[cc0,0,m12_,0,0,0,m12_]:>-(\[Pi]^2/(24 m12))-Log[\[Mu]^2/m12]^2/(4 m12)/;zeroChecks[{m12}], (* Double checked *)
C0iFin[cc1,0,m12_,0,0,0,m12_]:>2/m12+\[Pi]^2/(24 m12)+Log[\[Mu]^2/m12]/m12+Log[\[Mu]^2/m12]^2/(4 m12)/;zeroChecks[{m12}],
C0iFin[cc2,0,m12_,0,0,0,m12_]:>1/m12/;zeroChecks[{m12}], (* Double checked *)
C0iFin[cc00,0,m12_,0,0,0,m12_]:>1/2+1/4 Log[\[Mu]^2/m12]/;zeroChecks[{m12}], (* Double checked *)
C0iFin[cc11,0,m12_,0,0,0,m12_]:>-(7/(2 m12))-\[Pi]^2/(24 m12)-(3 Log[\[Mu]^2/m12])/(2 m12)-Log[\[Mu]^2/m12]^2/(4 m12)/;zeroChecks[{m12}],
C0iFin[cc12,0,m12_,0,0,0,m12_]:>-(1/(2 m12))/;zeroChecks[{m12}],
C0iFin[cc22,0,m12_,0,0,0,m12_]:>-(1/(4 m12))/;zeroChecks[{m12}],
C0iFin[cc001,0,m12_,0,0,0,m12_]:>-(2/9)-1/12 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],
C0iFin[cc002,0,m12_,0,0,0,m12_]:>-(7/72)-1/12 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],
C0iFin[cc112,0,m12_,0,0,0,m12_]:>1/(3 m12)/;zeroChecks[{m12}],
(*C0iFin[cc122,0,m12_,0,0,0,m12_] covered by c112 (they differ by a factor of 4 )*)


C0iFin[cc0,0,m12_,m12_,0,0,m12_]:>1/m12-Log[\[Mu]^2/m12]/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc00,0,m12_,m12_,0,0,m12_]:>3/4+1/4 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],
C0iFin[cc22,0,m12_,m12_,0,0,m12_]:>-(1/(2 m12))/;zeroChecks[{m12}],
C0iFin[cc002,0,m12_,m12_,0,0,m12_]:>-(5/36)-1/12 Log[\[Mu]^2/m12]/;zeroChecks[{m12}],


C0iFin[cc0,m12_,0,m12_,0,m12_,m12_]:>Log[\[Mu]^2/m12]/(2 m12)/;zeroChecks[{m12}],
C0iFin[cc00,m12_,0,m12_,0,m12_,m12_]:>1/4+1/4 (Log[\[Mu]^2/m12])/;zeroChecks[{m12}],
C0iFin[cc1,m12_,0,m12_,0,m12_,m12_]:>1/(2m12)/;zeroChecks[{m12}],
C0iFin[cc2,m12_,0,m12_,0,m12_,m12_]:>1/(2m12)/;zeroChecks[{m12}],
C0iFin[cc11,m12_,0,m12_,0,m12_,m12_]:>-(1/(6 m12))/;zeroChecks[{m12}],
C0iFin[cc12,m12_,0,m12_,0,m12_,m12_]:>-(1/(12 m12))/;zeroChecks[{m12}],
C0iFin[cc22,m12_,0,m12_,0,m12_,m12_]:>-(1/(6 m12))/;zeroChecks[{m12}],



(* Two scales *)
C0iFin[cc0,m12_,0,m22_,0,0,0]:>Log[-(\[Mu]^2/m12)]^2/(2 (m12-m22))-Log[-(\[Mu]^2/m22)]^2/(2 (m12-m22))/;zeroChecks[{m12,m22}],

(*C0iFin[cc0,0,m12_,m22_,0,0,0]:>/;zeroChecks[{m12,m22}], covered by cc0:102000 above*)
C0iFin[cc2,0,m12_,m22_,0,0,0]:>Log[-(\[Mu]^2/m12)]/(m12-m22)-Log[-(\[Mu]^2/m22)]/(m12-m22)/;zeroChecks[{m12,m22}],
C0iFin[cc00,0,m12_,m22_,0,0,0]:>3/4+(m12 Log[-(\[Mu]^2/m12)])/(4 (m12-m22))-(m22 Log[-(\[Mu]^2/m22)])/(4 (m12-m22))/;zeroChecks[{m12,m22}],
C0iFin[cc12,0,m12_,m22_,0,0,0]:>1/(2 (m12-m22))+(m22 Log[-(\[Mu]^2/m12)])/(2 (-m12+m22)^2)-(m22 Log[-(\[Mu]^2/m22)])/(2 (-m12+m22)^2)/;zeroChecks[{m12,m22}],
C0iFin[cc22,0,m12_,m22_,0,0,0]:>-(Log[-(\[Mu]^2/m12)]/(2 (m12-m22)))+Log[-(\[Mu]^2/m22)]/(2 (m12-m22))/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,m12_,0,m22_,0,0]:>\[Pi]^2/(6 m12)+Log[-(m22/m12)]^2/(2 m12)+PolyLog[2,(m12+m22)/m12]/m12/;zeroChecks[{m12,m22}],

C0iFin[cc0,m12_,0,0,0,0,m22_]:>\[Pi]^2/(6 m12)+Log[-(m22/m12)]^2/(2 m12)+PolyLog[2,(m12+m22)/m12]/m12/;zeroChecks[{m12,m22}], (* Double checked *)
C0iFin[cc00,m12_,0,0,0,0,m22_]:>3/4+m22/(2 m12)+(m22 \[Pi]^2)/(12 m12)+(m22^2 \[Pi]^2)/(12 m12^2)+1/4 Log[-(m22/m12)]+(m22 Log[-(m22/m12)])/(2 m12)+(m22 Log[-(m22/m12)]^2)/(4 m12)+(m22^2 Log[-(m22/m12)]^2)/(4 m12^2)+1/4 Log[\[Mu]^2/m22]+(m22 PolyLog[2,(m12+m22)/m12])/(2 m12)+(m22^2 PolyLog[2,(m12+m22)/m12])/(2 m12^2)/;zeroChecks[{m12,m22}], (* Double checked *)
C0iFin[cc1,m12_,0,0,0,0,m22_]:>1/m12+(m22 \[Pi]^2)/(6 m12^2)+Log[-(m22/m12)]/m12+(m22 Log[-(m22/m12)]^2)/(2 m12^2)+(m22 PolyLog[2,(m12+m22)/m12])/m12^2/;zeroChecks[{m12,m22}], (* Double checked *)
C0iFin[cc2,m12_,0,0,0,0,m22_]:>-(2/m12)-((m12+2 m22) \[Pi]^2)/(6 m12^2)-(2 Log[-(m22/m12)])/m12-((m12+2 m22) Log[-(m22/m12)]^2)/(2 m12^2)-((m12+2 m22) PolyLog[2,(m12+m22)/m12])/m12^2/;zeroChecks[{m12,m22}], (* Double checked *)

C0iFin[cc0,0,m12_,0,0,0,m22_]:>Log[m22/(-m12+m22)]^2/(2 m12)+(Log[m22/(-m12+m22)] Log[\[Mu]^2/m22])/m12-PolyLog[2,m12/(m12-m22)]/m12/;zeroChecks[{m12,m22}],
C0iFin[cc1,0,m12_,0,0,0,m22_]:>2/m12+Log[m22/(-m12+m22)]/m12-(m22 Log[m22/(-m12+m22)])/m12^2-(m22 Log[m22/(-m12+m22)]^2)/(2 m12^2)+Log[\[Mu]^2/m22]/m12-(m22 Log[m22/(-m12+m22)] Log[\[Mu]^2/m22])/m12^2+(m22 PolyLog[2,m12/(m12-m22)])/m12^2/;zeroChecks[{m12,m22}],
C0iFin[cc2,0,m12_,0,0,0,m22_]:>1/m12+((m12-m22) Log[m22/(-m12+m22)])/m12^2/;zeroChecks[{m12,m22}],
C0iFin[cc00,0,m12_,0,0,0,m22_]:>3/4-m22/(4 m12)+1/4 Log[m22/(-m12+m22)]-(m22 Log[m22/(-m12+m22)])/(2 m12)+(m22^2 Log[m22/(-m12+m22)])/(4 m12^2)+1/4 Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,0,0,0,m12_,m22_]:>-(Log[m12/m22]/(m12-m22))/;zeroChecks[{m12,m22}],
C0iFin[cc00,0,0,0,0,m12_,m22_]:>3/8-(m12 Log[m12/m22])/(4 (m12-m22))+1/4 Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],

C0iFin[cc0,m12_,0,0,m22_,m22_,0]:>ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]]/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,m12_,0,0,m12_,m22_]:>ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}], (* Double checked *)
C0iFin[cc1,0,m12_,0,0,m12_,m22_]:>1/m12+DiscB[m12,Sqrt[m12],Sqrt[m22]]/m12+(m22 Log[m12/m22])/(2 m12^2)-(m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12/;zeroChecks[{m12,m22}],  (* Double checked *)
C0iFin[cc2,0,m12_,0,0,m12_,m22_]:>1/m12+DiscB[m12,Sqrt[m12],Sqrt[m22]]/m12-((2 m12-m22) Log[m12/m22])/(2 m12^2)-ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],  (* Double checked *)
C0iFin[cc00,0,m12_,0,0,m12_,m22_]:>1/2-m22/(4 m12)-(m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(4 m12)+(m22 Log[m12/m22])/(4 m12)-(m22^2 Log[m12/m22])/(8 m12^2)+1/4 Log[\[Mu]^2/m12]+1/2 m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],  (* Double checked *)
C0iFin[cc11,0,m12_,0,0,m12_,m22_]:>-((m12+6 m22)/(4 m12^2))-(3 m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12^2)+((2 m12-3 m22) m22 Log[m12/m22])/(4 m12^3)+(m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12^2/;zeroChecks[{m12,m22}],
C0iFin[cc12,0,m12_,0,0,m12_,m22_]:>-((m12+2 m22)/(2 m12^2))-((m12+m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/m12^2+((m12-m22) m22 Log[m12/m22])/(2 m12^3)+(2 m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12/;zeroChecks[{m12,m22}],
C0iFin[cc22,0,m12_,0,0,m12_,m22_]:>-((9 m12-2 m22)/(4 m12^2))-((4 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12^2)+((6 m12^2-6 m12 m22+m22^2) Log[m12/m22])/(4 m12^3)+ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],
C0iFin[cc001,0,m12_,0,0,m12_,m22_]:>-(7/72)+m22/(4 m12)+m22^2/(6 m12^2)+(m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(3 m12)+(m22^2 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(6 m12^2)+(m22^3 Log[m12/m22])/(12 m12^3)-1/12 Log[\[Mu]^2/m12]-(m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/(2 m12)/;zeroChecks[{m12,m22}],
C0iFin[cc002,0,m12_,0,0,m12_,m22_]:>-(2/9)+(5 m22)/(8 m12)-m22^2/(12 m12^2)+(7 m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12)-(m22^2 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(12 m12^2)-(m22 Log[m12/m22])/(2 m12)+(3 m22^2 Log[m12/m22])/(8 m12^2)-(m22^3 Log[m12/m22])/(24 m12^3)-1/12 Log[\[Mu]^2/m12]-1/2 m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],
C0iFin[cc112,0,m12_,0,0,m12_,m22_]:>(m12^2+24 m12 m22+12 m22^2)/(12 m12^3)+(m22 (5 m12+2 m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12^3)-(m22 (2 m12^2-m12 m22-2 m22^2) Log[m12/m22])/(4 m12^4)-(3 m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12^2/;zeroChecks[{m12,m22}],
C0iFin[cc122,0,m12_,0,0,m12_,m22_]:>(4 m12^2+39 m12 m22-6 m22^2)/(12 m12^3)+((2 m12^2+6 m12 m22-m22^2) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12^3)-(m22 (8 m12^2-8 m12 m22+m22^2) Log[m12/m22])/(4 m12^4)-(3 m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,0,m12_,m22_,0,m22_]:>ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]]/;zeroChecks[{m12,m22}],

C0iFin[cc00,0,m12_,m12_,0,0,m22_]:>1/2+m22/(4 m12)+1/4 Log[m22/(-m12+m22)]-(m22^2 Log[m22/(-m12+m22)])/(4 m12^2)+1/4 Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,m12_,0,0,m22_,m22_]:>ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]]/;zeroChecks[{m12,m22}],
C0iFin[cc1,0,m12_,0,0,m22_,m22_]:>1/m12+DiscB[m12,Sqrt[m22],Sqrt[m22]]/m12-(m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12/;zeroChecks[{m12,m22}],
C0iFin[cc2,0,m12_,0,0,m22_,m22_]:>1/m12+DiscB[m12,Sqrt[m22],Sqrt[m22]]/m12-(m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12/;zeroChecks[{m12,m22}],
C0iFin[cc00,0,m12_,0,0,m22_,m22_]:>3/4-m22/(2 m12)+1/4 DiscB[m12,Sqrt[m22],Sqrt[m22]]-(m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(2 m12)+1/4 Log[\[Mu]^2/m22]+(m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/(2 m12)/;zeroChecks[{m12,m22}],
C0iFin[cc001,0,m12_,0,0,m22_,m22_]:>-(2/9)+m22/(24 m12)+m22^2/(2 m12^2)-1/12 DiscB[m12,Sqrt[m22],Sqrt[m22]]+(m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(12 m12)+(m22^2 DiscB[m12,Sqrt[m22],Sqrt[m22]])/(2 m12^2)-1/12 Log[\[Mu]^2/m22]-(m22^3 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/(2 m12^2)/;zeroChecks[{m12,m22}],
(*C0iFin[cc002,0,m12_,0,0,m22_,m22_]:>/;zeroChecks[{m12,m22}], ( Covered by cc001)*)
C0iFin[cc12,0,m12_,0,0,m22_,m22_]:>(m12-4 m22)/(2 m12^2)-(2 m22 DiscB[m12,Sqrt[m22],Sqrt[m22]])/m12^2+(2 m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12^2/;zeroChecks[{m12,m22}],
C0iFin[cc112,0,m12_,0,0,m22_,m22_]:>-((2 m12^2-3 m12 m22-36 m22^2)/(12 m12^3))+(m22 (m12+6 m22) DiscB[m12,Sqrt[m22],Sqrt[m22]])/(2 m12^3)-(3 m22^3 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12^3/;zeroChecks[{m12,m22}],
C0iFin[cc122,0,m12_,0,0,m22_,m22_]:>-((2 m12^2-3 m12 m22-36 m22^2)/(12 m12^3))+(m22 (m12+6 m22) DiscB[m12,Sqrt[m22],Sqrt[m22]])/(2 m12^3)-(3 m22^3 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12^3/;zeroChecks[{m12,m22}],
C0iFin[cc22,0,m12_,0,0,m22_,m22_]:>-((3 m12+4 m22)/(4 m12^2))-((m12+2 m22) DiscB[m12,Sqrt[m22],Sqrt[m22]])/(2 m12^2)+(m22^2 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m22]])/m12^2/;zeroChecks[{m12,m22}],


C0iFin[cc0,0,m12_,0,0,m22_,m12_]:>ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],
C0iFin[cc1,0,m12_,0,0,m22_,m12_]:>1/m12+DiscB[m12,Sqrt[m12],Sqrt[m22]]/m12-((2 m12-m22) Log[m12/m22])/(2 m12^2)-ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]]/;zeroChecks[{m12,m22}],
C0iFin[cc2,0,m12_,0,0,m22_,m12_]:>1/m12+DiscB[m12,Sqrt[m12],Sqrt[m22]]/m12+(m22 Log[m12/m22])/(2 m12^2)-(m22 ScalarC0[0,0,m12,Sqrt[m22],0,Sqrt[m12]])/m12/;zeroChecks[{m12,m22}],

C0iFin[cc0,0,m12_,m12_,0,0,m22_]:>-(Log[m22/(-m12+m22)]/(m12-m22))-(m22 Log[m22/(-m12+m22)])/(m12 (m12-m22))-Log[\[Mu]^2/m22]/(m12-m22)/;zeroChecks[{m12,m22}],
C0iFin[cc22,0,m12_,m12_,0,0,m22_]:>(m12-2 m22)/(2 m12^2)-((m12-m22) m22 Log[m22/(-m12+m22)])/m12^3/;zeroChecks[{m12,m22}],
C0iFin[cc002,0,m12_,m12_,0,0,m22_]:>-(5/36)-m22/(6 m12)+m22^2/(6 m12^2)-1/12 Log[m22/(-m12+m22)]+(m22^2 Log[m22/(-m12+m22)])/(4 m12^2)-(m22^3 Log[m22/(-m12+m22)])/(6 m12^3)-1/12 Log[\[Mu]^2/m22]/;zeroChecks[{m12,m22}],

C0iFin[cc00,m12_,0,m12_,0,m22_,m22_]:>(2 m12-m22)/(4 m12)+((m12-m22)^2 Log[m22/(-m12+m22)])/(4 m12^2)+1/4 (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],
C0iFin[cc1,m12_,0,m12_,0,m22_,m22_]:>1/(2 m12)+((m12-m22) Log[m22/(-m12+m22)])/(2 m12^2)/;zeroChecks[{m12,m22}],
C0iFin[cc2,m12_,0,m12_,0,m22_,m22_]:>1/(2 m12)+((m12-m22) Log[m22/(-m12+m22)])/(2 m12^2)/;zeroChecks[{m12,m22}],
C0iFin[cc11,m12_,0,m12_,0,m22_,m22_]:>-((3 m12-2 m22)/(6 m12^2))-((m12-m22)^2 Log[m22/(-m12+m22)])/(3 m12^3)/;zeroChecks[{m12,m22}],
C0iFin[cc12,m12_,0,m12_,0,m22_,m22_]:>-((3 m12-2 m22)/(12 m12^2))-((m12-m22)^2 Log[m22/(-m12+m22)])/(6 m12^3)/;zeroChecks[{m12,m22}],
C0iFin[cc22,m12_,0,m12_,0,m22_,m22_]:>-((3 m12-2 m22)/(6 m12^2))-((m12-m22)^2 Log[m22/(-m12+m22)])/(3 m12^3)/;zeroChecks[{m12,m22}],

C0iFin[cc0,m12_,0,m12_,m22_,m12_,m12_]:>DiscB[m12,Sqrt[m12],Sqrt[m22]]/(4 m12-m22)-Log[m12/m22]/(2 m12)/;zeroChecks[{m12,m22}],
C0iFin[cc00,m12_,0,m12_,m22_,m12_,m12_]:>(m12+m22)/(4 m12)+(m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(4 m12)-((2 m12^2+2 m12 m22-m22^2) Log[m12/m22])/(8 m12^2)+1/4 (Log[\[Mu]^2/m22])/;zeroChecks[{m12,m22}],

C0iFin[cc1,m12_,0,m12_,m22_,m12_,m12_]:>1/(2 m12)+((2 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12 (4 m12-m22))+(m22 Log[m12/m22])/(4 m12^2)/;zeroChecks[{m12,m22}],
C0iFin[cc2,m12_,0,m12_,m22_,m12_,m12_]:>1/(2 m12)+((2 m12-m22) DiscB[m12,Sqrt[m12],Sqrt[m22]])/(2 m12 (4 m12-m22))+(m22 Log[m12/m22])/(4 m12^2)/;zeroChecks[{m12,m22}],
C0iFin[cc11,m12_,0,m12_,m22_,m12_,m12_]:>-((m12+2 m22)/(6 m12^2))-((3 m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(3 m12^2 (4 m12-m22))+((m12-m22) m22 Log[m12/m22])/(6 m12^3)/;zeroChecks[{m12,m22}],
C0iFin[cc12,m12_,0,m12_,m22_,m12_,m12_]:>-((m12+2 m22)/(12 m12^2))-((3 m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(6 m12^2 (4 m12-m22))+((m12-m22) m22 Log[m12/m22])/(12 m12^3)/;zeroChecks[{m12,m22}],
C0iFin[cc22,m12_,0,m12_,m22_,m12_,m12_]:>-((m12+2 m22)/(6 m12^2))-((3 m12-m22) m22 DiscB[m12,Sqrt[m12],Sqrt[m22]])/(3 m12^2 (4 m12-m22))+((m12-m22) m22 Log[m12/m22])/(6 m12^3)/;zeroChecks[{m12,m22}],

(* Three Scales *)
C0iFin[cc0,m12_,0,0,m22_,m22_,m32_]:>ScalarC0[0,0,m12,Sqrt[m22],Sqrt[m32],Sqrt[m22]]/;zeroChecks[{m12,m22,m32}],



(***********************************)
(* D0iFin integrals                *)
(***********************************)
(* Scaleless *)

(* One scale *)
D0iFin[dd0,0,0,0,0,0,0,0,m12_,0,0]:>1/m12^2+Log[\[Mu]^2/m12]/m12^2/;zeroChecks[{m12}],
(*D0iFin[dd00,0,0,0,0,0,0,0,m12_,0,0]:>1/(4 m12)+Log[\[Mu]^2/m12]/(4 m12)/;zeroChecks[{m12}],*) (* WARNING: PACKAGE X GIVES THE WRONG RESULT HERE I THINK *)
D0iFin[dd00,0,0,0,0,0,0,0,m12_,0,0]:>3/(8 m12)+Log[\[Mu]^2/m12]/(4 m12)/;zeroChecks[{m12}],


D0iFin[dd0,0,0,0,0,0,0,0,0,0,m12_]:>1/m12^2+Log[\[Mu]^2/m12]/m12^2/;zeroChecks[{m12}],
D0iFin[dd1,0,0,0,0,0,0,0,0,0,m12_]:>-(3/(4 m12^2))-Log[\[Mu]^2/m12]/(2 m12^2)/;zeroChecks[{m12}],
D0iFin[dd00,0,0,0,0,0,0,0,0,0,m12_]:>3/(8 m12)+Log[\[Mu]^2/m12]/(4 m12)/;zeroChecks[{m12}],
D0iFin[dd11,0,0,0,0,0,0,0,0,0,m12_]:>11/(18 m12^2)+Log[\[Mu]^2/m12]/(3 m12^2)/;zeroChecks[{m12}],
(*D0iFin[dd12,0,0,0,0,0,0,0,0,0,m12_]:>11/(36 m12^2)+Log[\[Mu]^2/m12]/(6 m12^2)/;zeroChecks[{m12}],*) (* covered by d11*)
D0iFin[dd13,0,0,0,0,0,0,0,0,0,m12_]:>-(17/(36 m12^2))-Log[\[Mu]^2/m12]/(6 m12^2)/;zeroChecks[{m12}],
(*D0iFin[dd23,0,0,0,0,0,0,0,0,0,m12_]:>-(17/(36 m12^2))-1/(6 eIR m12^2)-Log[\[Mu]^2/m12]/(6 m12^2)/;zeroChecks[{m12}],*) (* Covered by dd13*)


(* Two scales *)
D0iFin[dd0,0,0,0,0,m12_,m22_,0,0,0,0]:>-((4 \[Pi]^2)/(3 m12 m22))+(2 Log[-(\[Mu]^2/m12)] Log[-(\[Mu]^2/m22)])/(m12 m22)/;zeroChecks[{m12,m22}],




D0iFin[dd0,0,0,0,0,0,0,0,0,m12_,m22_]:>1/(m12 (m12-m22))-1/((m12-m22) m22)-Log[m12/\[Mu]^2]/(m12 (m12-m22))+Log[m22/\[Mu]^2]/((m12-m22) m22)/;zeroChecks[{m12,m22}],
D0iFin[dd1,0,0,0,0,0,0,0,0,m12_,m22_]:>-(3/(4 m12 (m12-m22)))+3/(4 (m12-m22) m22)+Log[m12/\[Mu]^2]/(2 m12 (m12-m22))-Log[m22/\[Mu]^2]/(2 (m12-m22) m22)/;zeroChecks[{m12,m22}],
D0iFin[dd2,0,0,0,0,0,0,0,0,m12_,m22_]:>-((-m12+m22)/(2 m12 (m12-m22)^2))-Log[m12/m22]/(2 (m12-m22)^2)/;zeroChecks[{m12,m22}],
D0iFin[dd00,0,0,0,0,0,0,0,0,m12_,m22_]:>-(Log[m12/m22]/(4 (m12-m22)))/;zeroChecks[{m12,m22}],
D0iFin[dd11,0,0,0,0,0,0,0,0,m12_,m22_]:>11/(18 m12 (m12-m22))-11/(18 (m12-m22) m22)-Log[m12/\[Mu]^2]/(3 m12 (m12-m22))+Log[m22/\[Mu]^2]/(3 (m12-m22) m22)/;zeroChecks[{m12,m22}],
D0iFin[dd12,0,0,0,0,0,0,0,0,m12_,m22_]:>(-m12+m22)/(6 m12 (m12-m22)^2)+Log[m12/m22]/(6 (m12-m22)^2)/;zeroChecks[{m12,m22}],
D0iFin[dd13,0,0,0,0,0,0,0,0,m12_,m22_]:>1/(6 m12 m22-6 m22^2)-Log[m12/m22]/(6 (m12-m22)^2)/;zeroChecks[{m12,m22}],
D0iFin[dd23,0,0,0,0,0,0,0,0,m12_,m22_]:>-(1/(3 (m12-m22)^2))+((m12+m22) Log[m12/m22])/(6 (m12-m22)^3)/;zeroChecks[{m12,m22}],


(* Three scales *)
D0iFin[dd0,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(\[Pi]^2/(2 m22 m32))-(2 DiLog[-((m12-m22)/m22),m12-m22])/(m22 m32)-(2 DiLog[-((m12-m32)/m32),m12-m32])/(m22 m32)-Log[-(\[Mu]^2/m12)]^2/(m22 m32)+(2 Log[-(\[Mu]^2/m22)] Log[-(\[Mu]^2/m32)])/(m22 m32)/;zeroChecks[{m12,m22,m32}],
D0iFin[dd2,0,0,0,m12_,m22_,m32_,0,0,0,0]:>((3 m12-m22-3 m32) \[Pi]^2)/(12 m22 (m12-m22-m32) m32)+((m12-m32) DiLog[-((m12-m22)/m22),m12-m22])/(m22 (m12-m22-m32) m32)+((m12-m32) DiLog[-((m12-m32)/m32),m12-m32])/(m22 (m12-m22-m32) m32)+(m12 Log[-(\[Mu]^2/m12)]^2)/(2 (m12-m22) m22 m32)+Log[-(\[Mu]^2/m22)]^2/(2 (m12-m22) (m12-m22-m32))-((m12-m32) Log[-(\[Mu]^2/m22)] Log[-(\[Mu]^2/m32)])/(m22 (m12-m22-m32) m32)+Log[-(\[Mu]^2/m32)]^2/(2 (m12-m22-m32) m32)/;zeroChecks[{m12,m22,m32}],
D0iFin[dd3,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(\[Pi]^2/(6 (m12-m22-m32) m32))-DiLog[-((m12-m22)/m22),m12-m22]/((m12-m22-m32) m32)-DiLog[-((m12-m32)/m32),m12-m32]/((m12-m22-m32) m32)-Log[-(\[Mu]^2/m12)]^2/(2 (m12-m22) m32)-Log[-(\[Mu]^2/m22)]^2/(2 (m12-m22) (m12-m22-m32))+(Log[-(\[Mu]^2/m22)] Log[-(\[Mu]^2/m32)])/((m12-m22-m32) m32)-Log[-(\[Mu]^2/m32)]^2/(2 (m12-m22-m32) m32)/;zeroChecks[{m12,m22,m32}],
D0iFin[dd00,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(\[Pi]^2/(12 (m12-m22-m32)))-DiLog[-((m12-m22)/m22),m12-m22]/(2 (m12-m22-m32))-DiLog[-((m12-m32)/m32),m12-m32]/(2 (m12-m22-m32))-Log[-(\[Mu]^2/m22)]^2/(4 (m12-m22-m32))+(Log[-(\[Mu]^2/m22)] Log[-(\[Mu]^2/m32)])/(2 (m12-m22-m32))-Log[-(\[Mu]^2/m32)]^2/(4 (m12-m22-m32))/;zeroChecks[{m12,m22,m32}],
D0iFin[dd12,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(2/(m22 m32))-\[Pi]^2/(6 (m12-m22-m32)^2)-DiLog[-((m12-m22)/m22),m12-m22]/(m12-m22-m32)^2-DiLog[-((m12-m32)/m32),m12-m32]/(m12-m22-m32)^2+(m12 Log[-(\[Mu]^2/m12)])/(m22 (m12-m22-m32) m32)-Log[-(\[Mu]^2/m22)]^2/(2 (m12-m22-m32)^2)-((m12-m22) Log[-(\[Mu]^2/m32)])/(m22 (m12-m22-m32) m32)-Log[-(\[Mu]^2/m32)]^2/(2 (m12-m22-m32)^2)+Log[-(\[Mu]^2/m22)] (-((m12-m32)/(m22 (m12-m22-m32) m32))+Log[-(\[Mu]^2/m32)]/(m12-m22-m32)^2)/;zeroChecks[{m12,m22,m32}],
D0iFin[dd13,0,0,0,m12_,m22_,m32_,0,0,0,0]:>\[Pi]^2/(6 (m12-m22-m32)^2)+DiLog[-((m12-m22)/m22),m12-m22]/(m12-m22-m32)^2+DiLog[-((m12-m32)/m32),m12-m32]/(m12-m22-m32)^2-(m12 Log[-(\[Mu]^2/m12)])/((m12-m32) (m12-m22-m32) m32)+Log[-(\[Mu]^2/m22)]^2/(2 (m12-m22-m32)^2)+Log[-(\[Mu]^2/m32)]/((m12-m32) (m12-m22-m32))+Log[-(\[Mu]^2/m32)]^2/(2 (m12-m22-m32)^2)+Log[-(\[Mu]^2/m22)] (1/((m12-m22-m32) m32)-Log[-(\[Mu]^2/m32)]/(m12-m22-m32)^2)/;zeroChecks[{m12,m22,m32}],
D0iFin[dd22,0,0,0,m12_,m22_,m32_,0,0,0,0]:>(2 (m12-2 m22))/((m12-m22) m22 m32)-((3 m12^2-2 m12 m22+m22^2-6 m12 m32+2 m22 m32+3 m32^2) \[Pi]^2)/(12 m22 (m12-m22-m32)^2 m32)-((m12-m32)^2 DiLog[-((m12-m22)/m22),m12-m22])/(m22 (m12-m22-m32)^2 m32)-((m12-m32)^2 DiLog[-((m12-m32)/m32),m12-m32])/(m22 (m12-m22-m32)^2 m32)-(m12 (m12^2-m12 m22-m12 m32-m22 m32) Log[-(\[Mu]^2/m12)])/((m12-m22)^2 m22 (m12-m22-m32) m32)-(m12^2 Log[-(\[Mu]^2/m12)]^2)/(2 (m12-m22)^2 m22 m32)-((2 m12^2-2 m12 m22-2 m12 m32+m22 m32) Log[-(\[Mu]^2/m22)]^2)/(2 (m12-m22)^2 (m12-m22-m32)^2)+((m12-2 m22-m32) Log[-(\[Mu]^2/m32)])/(m22 (m12-m22-m32) m32)-((2 m12-m22-2 m32) Log[-(\[Mu]^2/m32)]^2)/(2 (m12-m22-m32)^2 m32)+Log[-(\[Mu]^2/m22)] ((m12^3-m12^2 m22-m12^2 m32-m22^2 m32)/((m12-m22)^2 m22 (m12-m22-m32) m32)+((m12-m32)^2 Log[-(\[Mu]^2/m32)])/(m22 (m12-m22-m32)^2 m32))/;zeroChecks[{m12,m22,m32}],
D0iFin[dd23,0,0,0,m12_,m22_,m32_,0,0,0,0]:>2/((m12-m22) m32)+((m12-m32) \[Pi]^2)/(6 (m12-m22-m32)^2 m32)+((m12-m32) DiLog[-((m12-m22)/m22),m12-m22])/((m12-m22-m32)^2 m32)+((m12-m32) DiLog[-((m12-m32)/m32),m12-m32])/((m12-m22-m32)^2 m32)+(m12 (m12-m22-2 m32) Log[-(\[Mu]^2/m12)])/((m12-m22)^2 (m12-m22-m32) m32)+(m12 Log[-(\[Mu]^2/m12)]^2)/(2 (m12-m22)^2 m32)+((m12^2-m22^2-m12 m32) Log[-(\[Mu]^2/m22)]^2)/(2 (m12-m22)^2 (m12-m22-m32)^2)+Log[-(\[Mu]^2/m32)]/((m12-m22-m32) m32)+((m12-m32) Log[-(\[Mu]^2/m32)]^2)/(2 (m12-m22-m32)^2 m32)+Log[-(\[Mu]^2/m22)] (-((m12^2-m12 m22-m12 m32-m22 m32)/((m12-m22)^2 (m12-m22-m32) m32))-((m12-m32) Log[-(\[Mu]^2/m32)])/((m12-m22-m32)^2 m32))/;zeroChecks[{m12,m22,m32}],
D0iFin[dd33,0,0,0,m12_,m22_,m32_,0,0,0,0]:>-(2/((m12-m22) m32))-(m22 \[Pi]^2)/(6 m32 (-m12+m22+m32)^2)-(m22 DiLog[-((m12-m22)/m22),m12-m22])/(m32 (-m12+m22+m32)^2)-(m22 DiLog[-((m12-m32)/m32),m12-m32])/(m32 (-m12+m22+m32)^2)-((m12 m22-m22^2-m12 m32-m22 m32) Log[-(\[Mu]^2/m12)])/((m12-m22)^2 (m12-m22-m32) m32)-(m22 Log[-(\[Mu]^2/m12)]^2)/(2 (-m12+m22)^2 m32)-(m22 (2 m12-2 m22-m32) Log[-(\[Mu]^2/m22)]^2)/(2 (m12-m22)^2 (m12-m22-m32)^2)-Log[-(\[Mu]^2/m32)]/((m12-m22-m32) m32)-(m22 Log[-(\[Mu]^2/m32)]^2)/(2 m32 (-m12+m22+m32)^2)+Log[-(\[Mu]^2/m22)] ((m22 (m12-m22-2 m32))/((m12-m22)^2 (m12-m22-m32) m32)+(m22 Log[-(\[Mu]^2/m32)])/(m32 (-m12+m22+m32)^2))/;zeroChecks[{m12,m22,m32}]
};


discRep$internal={
DiscB[a_,Sqrt[a_],Sqrt[b_]]:>(Sqrt[b (-4 a+b)] Log[(b+Sqrt[b (-4 a+b)])/(2 Sqrt[a] Sqrt[b])])/a/;zeroChecks[{a,b}],
DiscB[a_,Sqrt[b_],Sqrt[b_]]:>(Sqrt[a (a-4 b)] Log[(-a+Sqrt[a (a-4 b)]+2 b)/(2 b)])/a/;zeroChecks[{a,b}]
};


scalarC0Rep$internal={
(* One scale *)
(* Two scales *)
ScalarC0[0,0,m12_,Sqrt[m22_],0,Sqrt[m12_]]:>-(\[Pi]^2/(6 m12))-Log[(-m22+Sqrt[m22 (-4 m12+m22)])/(2 m12-m22+Sqrt[m22 (-4 m12+m22)])]^2/(2 m12)+PolyLog[2,-((2 m12)/(-m22-Sqrt[m22 (-4 m12+m22)]))]/m12-PolyLog[2,(2 m12)/(2 m12-m22+Sqrt[m22 (-4 m12+m22)])]/m12/;zeroChecks[{m12,m22}],
ScalarC0[0,0,m12_,Sqrt[m22_],0,Sqrt[m22_]]:>-(\[Pi]^2/(6 m12))-Log[(m12+Sqrt[m12 (m12-4 m22)])/(2 m12)]^2/(2 m12)+Log[(-m12+Sqrt[m12 (m12-4 m22)]+2 m22)/(m12+Sqrt[m12 (m12-4 m22)])]^2/(2 m12)+PolyLog[2,1-m12/m22]/m12+PolyLog[2,(2 m12-2 m22)/(m12+Sqrt[m12 (m12-4 m22)])]/m12-PolyLog[2,(2 m22)/(m12+Sqrt[m12 (m12-4 m22)])]/m12-PolyLog[2,-((2 (-m12+m22))/(m12+Sqrt[m12 (m12-4 m22)]-2 m22))]/m12+PolyLog[2,(2 m22)/(-m12+Sqrt[m12 (m12-4 m22)]+2 m22)]/m12/;zeroChecks[{m12,m22}],
(* Three scales *)
ScalarC0[0,0,m12_,Sqrt[m22_],m32_,Sqrt[m22_]]:>PolyLog[2,-((2 (m22-m32^2))/(m12-Sqrt[m12 (m12-4 m22)]-2 m22+2 m32^2))]/m12-PolyLog[2,(2 (m12-m22+m32^2))/(m12-Sqrt[m12 (m12-4 m22)]-2 m22+2 m32^2)]/m12+PolyLog[2,-((2 (m22-m32^2))/(m12+Sqrt[m12 (m12-4 m22)]-2 m22+2 m32^2))]/m12-PolyLog[2,(2 (m12-m22+m32^2))/(m12+Sqrt[m12 (m12-4 m22)]-2 m22+2 m32^2)]/m12-PolyLog[2,(m22-m32^2)^2/(m22^2+m12 m32^2-2 m22 m32^2+m32^4)]/m12+PolyLog[2,((m22-m32^2) (-m12+m22-m32^2))/(m22^2+m12 m32^2-2 m22 m32^2+m32^4)]/m12/;zeroChecks[{m12,m22,m32}]
};


int0[expr_]:= expr/.int0Reps;

intDiv[expr_]:= expr/.intDivReps;

intFin[expr_]:=expr/.intFinReps;

intCancel[expr_]:=expr/.intCancelReps;

discRep[expr_]:=expr/.discRep$internal;

scalarC0Rep[expr_]:=expr/.scalarC0Rep$internal;


End[]


EndPackage[]
