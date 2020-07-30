
# coding: utf-8
from ore_algebra import DifferentialOperators
from sage.rings.rational_field import QQ
from ore_algebra.analytic.bounds import *
from sage.rings.real_arb import RealBallField


def sign(x):
    return (x>0)-(x<0)
#Dans cette partie se trouvent toutes les outils essentiels et élémentaires à notre code
def sum(Pol1,Pol2,h):
#Calcule la somme de deux polynômes
    Pol=0
    for i in range (h):
        Pol+=(Pol1[i]+Pol2[i])*x^i
    return Pol

def product(M,u,n):
#produit d'une matrice par un vecteur dans RBF sans perte de précision
    v=[]
    print(M)
    print(u)
    for i in range (n):
        sol=0
        for j in range(n):
            print()
            sol+=M[i,j]*u[j]
        v.append(sol)
    return v

def translate_ini(dop,ini,x,epsilon):
#Renvoie le développement limité de f en x à l'ordre k ordre de dop.
    n=len(ini)
    ini_to_DSE(ini,n)
    M=dop.numerical_transition_matrix([0,x],epsilon)
    v=product(M,ini,n)
    return v
#Remarque cette fonction est utile si l'on veut les conditions initiale, mais
#dans le cas où ord(dop)<2 on n'a pas la dérivée bien évaluée. On peut la
#Récupérer à partir de l'équation différentielle.

def ini_to_DSE(ini,n):
#de f(x),...,f^(n-1)(x) -> f(x)/0!,...,f^(n-1)(x)/(n-1)!
    for k in range(n):
        ini[k]/=factorial(k)

def DSE_to_ini(ini,n):
#f(x)/0!,...,f^(n-1)(x)/(n-1)! -> f(x),...,f^(n-1)(x)
    for k in range(n):
        ini[k]*=factorial(k)

def to_sequential_op(A,dop):
#transforme dop en opérateur différentiel
    Rn.<n> = QQ['n']
    OreAlgebra(Rn, 'Sn')
    return dop.to_S(A)


#def majore_n_dernier_coeff():
"""
sage: dop=Dx^4+3*x^10*Dx+x^3-3
sage: diff_dop(dop)
Dx^5 + 3*x^10*Dx^2 + (90*x^9 + x^3 - 3)*Dx + 540*x^8 + 6*x^2
"""


def DSE(dop,ini,n,x):
#fonction qui évalue les n premiers coefficients du DSE de la fonction D-finie
    r=len(ini)-1 #condition d'arrêt
    coeffs=[ini[k]*factorial(k) for k in range (len(ini))]
    operator=dop
    coeff=operator.coefficients()
    exp=operator.exponents()
    while r<n:
        coeffs.append(extend_coeffdop(coeff,exp,ini,x))
        opertator=diff_dop(operator)
        coeff=operator.coefficients()
        exp=operator.exponents()
        r+=1
    for k in range (n+1):
        coeffs[k]= coeffs[k]/factorial(k)
    return coeffs

def extend_coeffdop(coeff,exp,ini,x):#n est la taille  de l'opérateur
#fonction prenant en paramètre un opérateur dop, des paramètres initiaux init
#et un nombre k étant le kème coefficient à calculer
    n=len(coeff)
    sol=0
    for i in range (n-1):
        sol+=ini[exp[i]]*coeff[i](x)
    sol=-sol/(coeff[n-1](x))
    return sol
r"""
un exemple qui marche
 Rn.<n> = QQ['n']; Rx.<x> = QQ['x']
....: sage: A.<Sn> = OreAlgebra(Rn, 'Sn')
....: sage: B.<Dx> = OreAlgebra(Rx, 'Dx')
sage: (Dx-1).to_S(A)
(n + 1)*Sn - 1

Un exemple qui marche moins bien

sage: dop=(1-x^2)*Dx^2-1
sage: Rx.<x> = QQ['x']
sage: B.<Dx> = OreAlgebra(Rx, 'Dx')
sage: dop=(1-x^2)*Dx^2-1
sage: dop.numerical_transition_matrix([0,i,3+i,3],1e-20)
[   [1.307818686187017226438 +/- 3.22e-22] + [3.760054349333636200978 +/- 5.21e-22]*I    [1.696050455566830862584 +/- 4.70e-22] + [2.780420408555851744543 +/- 4.98e-22]*I]
[ [-0.9502961786628460069257 +/- 3.14e-23] + [1.211859120812618032217 +/- 2.93e-22]*I [-0.4677638217023139947250 +/- 6.65e-23] + [0.8961247680898814220572 +/- 6.22e-23]*I]
"""

#Ici est la partie où commence réelement notre algorithme


def to_pol(DSE,k):
#Renvoie le polynome associé au calcul des coefficients
    x=QQ['x'].gen()
    pol=0
    for i in range (len(DSE)):
        pol+=DSE[i]*t^i
    return pol

def separation(RBF_list):
#sépare les balls pour plus de précision, mais majore la série des RBF
    mid=[]
    rad=[]
    for el in RBF_list:
        mid.append(el.mid())
        rad.append(RBF(el.rad()))
    return mid,rad

def power_serie_sol(dop,ini,n,ord):
#calcule une solution approchée de dop à partir de la série de Taylor à l'ordre n
    PSS=dop.power_series_solutions(n)
    s=0
    for i in range(ord):
        s+=ini[i]*PSS[ord-1-i]
    return s

def res_pol(pol,ord,n):
#transforme un polynôme dans la forme demandée dans normalized_residual
    coeff=pol.coefficients()
    n=len(coeff)
    res=[]
    for i in range(ord+1):
        res.append([abs(coeff[n-1-i])])
    return res

def res(dop,ini,n,ord):
#Donne le résidu d'une équation différentielle pour la forme normalized_residual
    PSS=power_serie_sol(dop,ini,n,ord)
    return res_pol(PSS,ord,n)

def majorant_rest(dop,ord,n,PSS):
#on crée ici la série majorante
    maj=DiffOpBound(dop,max_effort=2)
    return maj.tail_majorant(n,[maj.normalized_residual(n,res_pol(PSS,ord,n))])

def truncation(pol,h,l):
#Fonction découpant un polynôme en deux partie, la partie de degré inférieure à k
#et la partie de degré supérieure à k
    coeff=pol.coefficients()
    exp=pol.exponents()
    r1=0
    r2=0
    x=QQ['x'].gen()
    for i in range (l):
        if i<h:
            r1+=pol[i]*x^i
        else:
            r2+=pol[i]*x^i
    return r1,r2

################################################################################
#Dans cette partie on va travailler pour avoir une série majorante de la dérivée


def derivate_annulator(dop):
#Renvoie un polynôme annulateur de la dérivée
    n=dop.coefficients()[0].degree()
    operator=dop
    for i in range(n+1):
        operator=diff_dop(operator)
        print(operator)
    return derivate_dop_Dx(operator)


def diff_dop(dop):
#renvoie la dérivée de l'opérateur dop
    coeff=dop.coefficients()
    exp=dop.exponents()
    n=len(coeff)
    ddop=0
    for i in range(n):
        ddop+=Dx^(exp[i])*diff(coeff[i],x)+Dx^(exp[i]+1)*coeff[i]
    return ddop

def derivate_dop_Dx(dop):
#différencie par rapport à Dx
    coeff=dop.coefficients()
    print(coeff)
    exp=dop.exponents()
    print(exp)
    n=len(coeff)
    ddop=0
    for i in range(n):
        ddop+=Dx^(exp[i]-1)*coeff[i]
    return ddop

################################################################################

#########################Travail sur RBF########################
def real(r_b):
#Transforme un RBF en un majorant de celui-ci
    return r_b.mid()+r_b.rad()
def abs_pol(pol,l):
#récupère le majorant idéal du polynôme pol
    x=QQ['x'].gen()
    p=0
    for i in range(l):
        p+=abs(pol[i])*x^i
    return p

def maj_rbf(pol,l):
#récupère la série maj parfaite de pol
    x=QQ['x'].gen()
    P=0
    for i in range(l):
        P+=(abs(pol[i].mid())+pol[i].rad())*x^i
    return P


r"""
_Majorant_ renvoie un résultat de la forme: f(x)t+...+(f^(n-1)(x)/k!)t^(n-1),
|f^(n)(x)/n!|t^(n-1)+...+|f^(n+k)(x)/n+k!|t^(n+k),eps((1-t^(n+k+1))/(1-t)),
M^(n+k+1)(f+eps(x^(n+k+1)/(1-x)),x)(t)
exemple:
from ore_algebra import DifferentialOperators
from sage.rings.rational_field import QQ
from ore_algebra.analytic.bounds import *
Rx.<x> = QQ['x']
A.<Dx> = OreAlgebra(Rx, 'Dx')
dop=Dx^2+1
_Majorant_(1,10,dop,[1,0],3,1e-10)
 2.7281539258e-7*x^10 + 3.8888891110e-7*x^9 + 0.000024553385332*x^8 +
 0.000028000001599*x^7 + 0.0013749895786*x^6 + 0.0011760000672*x^5 +
 0.041249687358*x^4 + 0.023520001343*x^3 + 0.49499624830*x^2 + 0.14112000806*x,
 1.0214460e-18*x^10 + 2.6912496e-18*x^9 + 9.1930136e-17*x^8 + 1.9376997e-16*x^7
 + 5.1480876e-15*x^6 + 8.1383389e-15*x^5 + 1.5444263e-13*x^4 + 1.6276678e-13*x^3
  + 1.8533115e-12*x^2 + 9.7660067e-13*x + 3.7066231e-12,
 (x^11*[2.06678327712620e-9 +/- 3.12e-24]*x +
 [3.53535373727012e-9 +/- 4.36e-24])*exp(int([0.1000000008815815 +/- 2.00e-17]*x)),
 (x^11*[7.738226947412430e-21 +/- 5.57e-38]*x +
 [2.44659058386122e-20 +/- 2.23e-35])*exp(int([0.1000000008815815 +/- 2.00e-17]*x)))
"""
def _Majorant_(n,k,dop,ini,x,eps):
    order=len(ini)
    if x==0:
        PSS_ini=power_serie_sol(dop,ini,n+k,order)
        M_nk_ini=majorant_rest(dop,order,n+k,PSS_ini)
        left_ini,right_ini=truncation(PSS_ini,n,n+k)
        return left_ini,abs_pol(right_ini,n+k),0,M_nk_ini,0
    else:
        new_ini,new_eps=separation(translate_ini(dop,ini,x,eps))#translation des paramètres donc RBF, séparation de la RBF
        PSS_new_ini=power_serie_sol(dop,new_ini,n+k,order)
        PSS_new_eps=power_serie_sol(dop,new_eps,n+k,order)
        M_nk_ini=majorant_rest(dop,order,n+k,PSS_new_ini)
        M_nk_eps=majorant_rest(dop,order,n+k,PSS_new_eps)
        left_ini,right_ini=truncation(PSS_new_ini,n,n+k)
        return left_ini,abs_pol(right_ini,n+k),maj_rbf(PSS_new_eps,n+k),M_nk_ini,M_nk_eps

"""
Remarque: Nous sommes obligés d'avoir tous ces paramètre pour pouvoir fixer la
précision de la série majorantes
"""

def evaluate(left_ini,right_ini,PSS_new_eps,M_nk_ini,M_nk_eps,n,t,x):
#Évaluation de la fonction M définie dans le rapport de stage
    if x==0:
        if n==1:
            return sign(left_ini)*left_ini-right_ini(t)-real(M_nk_ini.bound(RBF(t)))
        else:
            return abs(left_ini(t))-right_ini(t)-real(M_nk_ini.bound(RBF(t)))
    else:
        if n==1:
            return sign(left_ini)*left_ini-PSS_new_eps(t)-right_ini(t)-real(M_nk_ini.bound(RBF(t)))-real(M_nk_eps.bound(RBF(t)))
        else:
            return abs(left_ini(t))-PSS_new_eps(t)-right_ini(t)-real(M_nk_ini.bound(RBF(t)))-real(M_nk_eps.bound(RBF(t)))


"""
Dans le cas M^1(f,x), on sait que la fonction est strictement décroissante, on a
donc un unique zéro
"""
def zero(f,eps):
#Recherche le premier zéro d'une fonction f décroissante
    a=0
    b=1
    n=0
    while f(b)>=0:
        a,b=b,2*b
    while (b-a)>eps:
        m=(a+b)/2
        if f(m)>=0:
            a=m
        else:
            b=a
    return a

              ####### Algorithmes principaux #########

def bissection(k,dop,ini,segment,prec):
    a,b=segment[0],segment[1]
    m=(a+b)/2
    d=(b-a)
    if d<prec:
        return [segment]
    else:
        eps=1e-5*prec
        #The following section is to fixe epsilon
        if m!=0:
            fm=dop.numerical_solution(ini,[0,m],eps)
            while (abs(fm.mid())-fm.rad())<1e5*fm.rad():
                eps*=1e-10
        #epsilon fixed
        left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(1,k,dop,ini,m,eps)
        def M(t):
            return evaluate(left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps,1,t,m)
        d/=2
        while M(d)<0:
            d/=2
        if d==(b-a)/2:
            return []
        else:
            return bissection(k,dop,ini,[a,m-d],prec)+bissection(k,dop,ini,[m+d,b],prec)


def S_(m,k,dop,ini,x,eps,t):
#algorithme de bissection_exclusion
    left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(m,k,dop,ini,x,eps)
    left,right=truncation(PSS_new_eps,2,len(PSS_new_eps))
    x=QQ['x'].gen()
    right,PSS_new_eps,M_nk=right*x^(-1),right_ini*x^(-1),M_nk*x^(-1)
    fm=left_ini[m-1]-left[m-1]
    if f1>0:
        return (right(t)+right_ini(t)+real(M_nk.bound(RBF(t))))<fm
    else:
        return False

def increasing(f,x,eps):
#vérifie que la fonction est croissante
    return (f(x+eps)-f(x))>0

def inclusion(dop,ini,x,prec):
#Fonction recherchant le max local le plus proche de 0 et regarde si il
#satisfait la condition du rapport.
    eps=1e-5*prec
    fx=dop.numerical_solution(ini,[0,x],eps)
    #The following section is to fixe epsilon
    if x!=0:
        while (abs(fx.mid())-fx.rad())<1e5*fx.rad():
            eps*=1e-10
    #epsilon fixed
            fm=dop.numerical_solution(ini,[0,m],eps)
    left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(2,10,dop,ini,x,eps)
    left_eps,right_eps=truncation(PSS_new_eps,2,PSS_new_eps.degree())
    f0=sign(left_ini[0])*left_ini[0]+left_eps[0]
    f1=sign(left_ini[1])*left_ini[1]-left_eps[1]
    def f(t):
        return f1*t-right_eps(t)-real(M_1k_ini.bound(RBF(t)))-real(M_1k_eps.bound(RBF(t)))-f0
    a=f0/f1
    b=max(16*a,256*prec)
    while b-a>3*prec and f(a)<=0 and f(b)<=0:
        m=(a+b)/2
        if croissante(f,m,eps):
            a=m
        else:
            b=m
    if f(b)>0:
        s=b
        while f(s/2)>0:
            s/=2
        return [b,s]
    if f(a)>0:
        s=a
        while f(s/2)>0:
            s/=2
        return [a,s]
    else:
        return [0,0]


def find_certified_zeros(dop,ini,segment,iteration=0,max_iteration=10):
#Fonction renvoyant la liste des zéros sous forme de liste de segment ou de real
#ball si ces zéros sont simples, sinon renvoie la liste des zéros certifiés
# et la liste des zéros de multiplicité supérieure

    k=10
    if segment==[]:
        return [[],[]]
    if iteration>max_iteration:
        return [[],segment]
    else:
        a,b=segment[0],segment[1]
        prec=min(1e-3*(b-a),1e-1)
        indeterminated=bissection(k,dop,ini,segment,prec)
        n=len(indeterminated)
        determinated=[False for k in range(n)]
        big_admitted=[]
        small_admitted=[]
        for i in range(n):
            x=indeterminated[i][1]
            l=inclusion(dop,ini,x,prec)
            if l[0]>0:
                big_admitted.append([x-l[0],x+l[0]])
                small_admitted.append([x-l[1],x+l[1]])
    still_indeterminate=still_indeterminated(big_admitted,indeterminated,determinated)
    admitte=admitted(dop,ini,small_admitted)
    if still_indeterminate==[]:
        return [admitte,[]]
    else:
        unsure=[[]]
        for i in range(len(still_indeterminated)):
            admitte,unsure=concatenate([admitte,unsure],find_certified_zeros(dop,ini,still_indeterminated[i],iteration+1,max_iteration))
    if unsure!=[[]]:
        print("possibliy a zero of multiplicity superior at 1, you can increase max_iteration")
        print("or test inclusion(dop,ini,x,prec,m) to test how many zeros there is possibly")
        print("in the intervalle")
    return [admitte,unsure]

def concatenate(sol1,sol2):
#sol1 et sol2 sont de la forme [admitted,unsure] où admitted est la liste des
#zéros certifiés de dop,ini, et unsure des segments non certifiés
    return (sol1[0]+sol2[0]),(sol1[1]+sol2[1])

def admitted(dop,ini,small_admitted):
#Renvoie un liste de segments disjoints à partir de la listes obtenues
    n=len(small_admitted)
    admitted=[]
    i=0
    while i<n-1:
        intersect=intersection(small_admitted[i],small_admitted[i+1])
        if intersect!=[]:
            admitted.append(intersect)
            i+=2
        else:
            admitted.append(small_admitted[i])
        "ok"
    return admitted

def admis(admis):
#Test si admis est bien disjoint
    for i in range(len(admis)-1):
        if admis[i][1]>admis[i][0]:
            return False
    return True

def intersection(segment1,segment2):
#les segments sont classés dans l'ordre croissant renvoie intersection revoie
#l'intersection des segments 1 et 2
    if segment1[1]<segment2[0]:
        return []
    else:
        return [segment2[0],segment1[1]]

def still_indeterminated(big_admitted,indeterminated,determinated):
#Renvoie la liste des intervalles encore indéterminés
    n=len(big_admitted)
    for i in range(len(big_admitted)):
        for j in range(n):
            if included(indeterminated[j],big_admitted[i]):
                determinated[i]=True
    still_ind=[]
    for i in range (n):
        if not determinated[i]:
            still_ind.append(indeterminated[i])
    return still_ind


def included(segment1,segment2):
#Renvoie si oui ou non segment1 est inclu dans segment2
    if segment1==[]:
        return True
    if segment2==[]:
        return False
    else:
        return (segment1[1]<=segment2[1])and(segment2[0]<=segment1[0])


def plot_D_finite_function(dop,ini,f,eps,a,b):
#Fonction qui plot la fonction f et la fonction M(f,x) dans l'intervalle [a,b]
    x=(a+b)/2
    left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(1,k,dop,ini,x,eps)
    def M(t):
        return evaluate(left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps,t,1,x)
    P1=plot(M(t),(t,a,b))
    P2=plot(f(t),(t,a,b))
    show(p1+p2)
