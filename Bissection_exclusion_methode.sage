from ore_algebra.dfinite_function import *
from ore_algebra import DifferentialOperators
from sage.rings.rational_field import QQ
from ore_algebra.analytic.bounds import *
from sage.rings.real_arb import RealBallField



#Dans cette partie se trouvent toutes les outils essentiels et élémentaires à notre code
def abs(list):
#transforme une liste en la liste de la valeur abs de ses coeffs
    l=[]
    for el in list:
        l.append(abs(el))
    return l
def product(M,u,n):
#produit d'une matrice par un vecteur dans RBF sans perte de précision
    v=[]
    for i in range (n):
        sol=0
        for j in range(n):
            sol+=M[i,j]*u[j]
        v.append(sol)
    return v

def translate_ini(dop,ini,x,epsilon):
#Renvoie le développement limité de f en x à l'ordre k ordre de dop.
    n=len(ini)
    ini_to_DSE(ini,n)
    M=dop.numerical_transition_matrix([0,x],epsilon)
    v=product(M,ini,n)
    DSE_to_ini(v,n)
        return v
#Remarque cette fonction est utile si l'on veut les conditions initiale, mais
#dans le cas où ord(dop)<2 on n'a pas la dérivée bien évaluée. On peut la
#Récupérer à partir de l'équation différentielle.

def ini_to_DSE(ini,n):
#de f(x),...,f^(n-1)(x) -> f(x)/0!,...,f^(n-1)(x)/(n-1)!
    for k in range(n):
        ini[k]/=factorial(k)

def DSE_to_ini(ini):
#f(x)/0!,...,f^(n-1)(x)/(n-1)! -> f(x),...,f^(n-1)(x)
    for k in range(n):
        ini[k]*=factorial(k)

def to_sequential_op(A,dop):
#transforme dop en opérateur différentiel
    Rn.<n> = QQ['n']
    OreAlgebra(Rn, 'Sn')
    return dop.to_S(A)

def separation(RBF_list):
#sépare les balls pour plus de précision
    mid=[]
    rad=[]
    for el in RBF_list:
        mid.append(el.mid())
        rad.append(el.rad())
    return mid,rad


#def majore_n_dernier_coeff():
"""
sage: dop=Dx^4+3*x^10*Dx+x^3-3
sage: diff_dop(dop)
Dx^5 + 3*x^10*Dx^2 + (90*x^9 + x^3 - 3)*Dx + 540*x^8 + 6*x^2
"""
def diff_dop(dop):
#renvoie la dérivée de l'opérateur dop
    coeff=dop.coefficients()
    exp=dop.exponents()
    n=len(coeff)
    ddop=0
    for i in range(n):
        ddop+=Dx^(exp[i])*diff(coeff[i],x)+Dx^(exp[i]+1)*coeff[i]
    return ddop

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
        print(sol)
    sol=-sol/(coeff[n-1](x))
    return sol
"""
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
def to_pol(DSE,k):
#Renvoie le polynome associé au calcul des coefficients
    t=QQ['t'].gen()
    pol=0
    for i in range (len(DSE)):
        pol+=DSE[i]*t^i
    return pol

#Ici est la partie où commence réelement notre algorithme


def last(DSE,n,s):
#Donne les indices de fn-1 à fn-s, n est aussi la taille de la liste DSE
    l=[]
    for i in range(n-1,n-s):
        l.append([DSE[i]])
    return l

def majorant_rest(dop,DSE,n,x,eps):
#on crée ici la série majorante
    translate_ini(dop, ini, eps)
    DSE=DSE(dop,ini,n,x)
    maj=DiffOpBound(dop,max_effort=2)
    res_list=[]
    s=dop.coefficients()[len(dop.coefficients())]
    return maj.normalized_residual(n,last(DSE,n))
