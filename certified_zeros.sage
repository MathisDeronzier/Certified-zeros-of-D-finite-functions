from ore_algebra.analytic import polynomial_approximation as polapprox
from sage.rings.rational_field import QQ

#Pour lire ce code de façon compréhensible on pose:
#Pol: est un polynôme
#eps: est un réel supérieur à zéro faisant référence à epsilon
#prec: fait référence à la précision aussi supérieure à zéro
#[a,b]: est un intervalle avec a<b
#dop: est une équation différentielle polynômial écrite sous la forme Dx^n+...
#ini: est la liste des conditions initiales

################################################################################
#Cette partie l'algorithme permet de trouver les zéros à partir de la méthode
#d'exclusion de Sturm
def sign(x):
#renvoie +1 si positif -1 si négatif 0 sinon
     return (x > 0) - (x < 0)

def Sturm_serie(Pol):
#calcule la série des polynômes de Sturm et la stock dans une liste
    Sturm_s=[Pol]
    Sturm_s.append(diff(Pol))
    k=0
    P=Sturm_s[0]%Sturm_s[1]
    while P!=0:
        Sturm_s.append(-P)
        k+=1
        P=Sturm_s[k]%Sturm_s[k+1]
    return (Sturm_s,k+2)

def sigma(Sturm_s,m,x):
#fonction sigma de Sturm
    signe=sign(Sturm_s[0](x))
    sigma=0
    for k in range (1,m):
        if signe==-sign(Sturm_s[k](x)):
            signe=-signe
            sigma+=1
    return sigma

#Théorème de Sturm
def zero_number(Sturm_s,m,a,b):
#Fonction renvoyant le nombre de zéros dans l'intervalle [a,b]
    return sigma(Sturm_s,m,a)-sigma(Sturm_s,m,b)

##On travaille ici sur les méthodes d'exclusion

#La méthode d'exclusion de Sturm est adaptée pour de "petits" intervalles
def Sturm_exclusion(Pol,a,b,prec):
#La fonction renvoit une liste d'intervalles à prec près du zéro
    (Sturm_s,n)=Sturm_serie(Pol)
    def Rec_Sturm_exclusion(a,b):
        d=b-a
        zeros=zero_number(Sturm_s,n,a,b)
        if d<=prec and zeros==1:
            return [[a,b]]
        if d>prec and zeros>0:
            m=(a+b)/2
            if Pol(m)==0:
                return Rec_Sturm_exclusion(a,m-prec/2)+\
                [[m-prec/2,m+prec/2]]+Rec_Sturm_exclusion(m+prec/2,b)
            else:
                return Rec_Sturm_exclusion(a,m) + Rec_Sturm_exclusion(m,b)
        return []
    return Rec_Sturm_exclusion(a,b)

#La méthode présentée dans l'article de Jakoubson semble plus efficace sur les
#grands intervalles.


################################################################################
#Cette partie servira à certifier les zéros trouvés par la fonction
#Sturm_exclusion

def Pol_To_TaylorPol(Pol,a):
##on crée un  polynôme de la forme f(a)+ t^1*f'(a)+...+t^n*f^(n)(a)=f(a+t)
#À partir d'un polynôme de la forme f(x)= a0+xa1+...+x^nan
    coeffs=list(Pol)
    m=len(coeffs)
    Px=[abs(Pol(a))]
    for n in range(1,m):
        Px.append(-abs(diff(Pol,n)(a))/factorial(n))
    t=QQ['t'].gen()
    P=0
    for i in range(m):
        P+=Px[i]*t^i
    return P

def first_zero(f,prec):
##renvoie la première fois où s'annule la fonction
    a,b=0,1
    while f(b)>0:
        a,b=b,2*b
    while b-a>prec:
        m=(a+b)/2
        if f(m)>0: a=m
        else: b=m
    return a

def alphaK(Pol,a,prec):
#renvoie un réel r tel que Dpol(a+r) soit encore de même signe que Dpol(a)
    return first_zero(Pol_To_TaylorPol(diff(Pol),a),prec)

##Méthode du gradient pour trouver un optimum locale
def sup_eps(Pol,x,eps,n=0):
#Fonction recherchant le max local le plus proche de a
#renvoyant True si ce max est supérieur à epsilon False sinon
    DPol=diff(Pol)
    Dfun=DPol(x)
    if Pol(x)>eps:
        return True
    if n>9:
        return False
    signe=sign(Dfun)#pour donner la direction
    x+=signe*alphaK(Pol,x,eps/8)
    return sup_eps(Pol,x,eps,n+1)

def certified_zero(Pol,x,eps):
#renvoie True si le zéro est certifié False sinon
    return sup_eps(Pol,x,eps) #and sup_eps(-Pol,x,eps))

################################################################################
##Définir la précision voulue pour que l'algorithme converge
#Théorie alpha-gamma de Smale

certificator=(13-3*sqrt(17))/4

#Corollaire du théoème de Wang-han Pour savoir si la méthode de Newton converge

def alpha(Pol,a):
    gamma=0
    DPol=Diff(Pol)(a)
    fact=1
    if DPol==0:
        return + infinity
    for k in range (2,Pol.degree()+1):
        fact*=k
        gamma=max(gamma,(abs(DPol^(-1)*diff(Pol,k)(a))/fact)^(1/k-1))
    return (DPol^(-1)*Pol(a)*gamma)<certificator
################################################################################

def find_certified_zeros_in_list(fun,list,eps):
#certifie les zéros de la liste
    l=[]
    for segm in list:
        mid=(segm[0]+segm[1])/2
        if certified_zero(fun,mid,eps):
            print(True,segm)
            l.append(mid)
        else:
            print(False, segm)
    return l

################################################################################
#Pour commencer le segment ne doit pas contenir de singularité non régulières
#sur cet intevalle les exeptions seront traitées plus tard

def arb_pol_To_pol(Pol):
#Convertit le polynôme définit sur l'anneau des boules en polynôme sur l'anneau
#sur lequel est défini 'l'anneau des boules
    P=0
    coeffs=list(Pol)
    t=RR['t'].gen()
    for k in range (len(coeffs)):
        P+=coeffs[k].mid()*t^k
    return P

def find_certified_zeros(dop,ini,segment,eps):
#renvoie les zéros certifiés à une précision eps près
    a,b=segment[0],segment[1]
    mid=(a+b)/2
    rad=(b-a)/2
    pol=polapprox.on_interval(dop,ini,[-mid,[-rad,+rad]],eps/2)
    P=arb_pol_To_pol(pol)
    l=Sturm_exclusion(P,-rad,rad,eps)
    certified=find_certified_zeros_in_list(P,l,eps/2)
    for zero in certified:
        zero+=mid
    return certified

################################################################################


def test(dop, ini, path, eps, rad=None):
    p=polapprox.on_interval(dop, ini, path, eps, rad=None)
    pol=arb_pol_To_pol(p)
    pt=plot(pol,-10,10)
    show(pt)
