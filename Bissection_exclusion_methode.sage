# coding: utf-8
from ore_algebra import DifferentialOperators
from sage.rings.rational_field import QQ
from ore_algebra.analytic.bounds import *
from sage.rings.real_arb import RealBallField

r""""
Each fonction is explain but notations are always used to represent the same
object, to make the reading of this code easier here the notations with
their mathematical meaning:
x,a,b,m: Reals or Rationals
M: Matrix
dop: a differential_operator, of the form Pr(x)*Dx^r+...+Po(x), Pi defiened
over K['x']
ini: [f^(0)(0),...,f^(r-1)(0)] where f^(i)(0) are in the same field K that
Po,...Pr
order=r the order of the differential equation
eps,prec: eps>0, prec>0, are precision in the computation
vect,v: are vectors
pol: a polynom
h,i,k,n,: int
PSS_: a power serie solution of the differential operator dop
"""

def sign(x):
#real x
#return -1 if x<0, 0 if x=0, +1 if x>0
    return (x>0)-(x<0)

################################################################################
#This section of the code is gathering the tools we'll need to manipulate
#The differential equation, the polynoms and manipluate RBF at high precision
################################################################################


######################Work over the translation of ini##########################
def product(M,vect,n):
#Require a matrix M in RBF[] or QQ,a vector vect, n=len(vect)=len(M)
#Return vectorial product M*vect without loosing precision
    v=[]
    for i in range (n):
        sol=0
        for j in range(n):
            sol+=M[i,j]*vect[j]
        v.append(sol)
    return v

def translate_ini(dop,ini,order,x,eps):
#Require
#return a vector v of the translated ini in 0 to ini in x
    ini_to_DSE(ini,order)
    M=dop.numerical_transition_matrix([0,x],eps)
    v=product(M,ini,order)
    return v


def ini_to_DSE(ini,n):
# Require: [f(x),...,f^(r-1)(x)] ,r
# Return: [f(x)/0!,...,f^(n-1)(x)/(n-1)!]
    for k in range(n):
        ini[k]/=factorial(k)

def recc_order(dop):
#Require a dop  Pr(x)*Dx^r+...+Po(x)
#Return the order of the Sequencial recurrence corresponding to this differential
#operator
    coeff=dop.coefficients()
    exp=dop.exponents()
    maxeq=-100000000000
    mineq=100000000000
    for i in range (len(exp)):
        pol=coeff[i]
        if pol in QQ:
            val=exp[i]
            maxeq=max(val,maxeq)
            mineq=min(val,mineq)
        else:
            maxeq=max(maxeq,exp[i]-coeff[i].exponents()[0])
            mineq=min(mineq,exp[i]-coeff[i].degree())
    return maxeq-mineq



def translate_pol(pol,t):
#Require a polynom pol and a real t
#return Pol(x+t)
    P=0
    x=QQ['x'].gen()
    deg=pol.degree()
    if deg==0:
        return pol
    else:
        for i in range (deg+1):
            P+=pol[i]*(x+t)^i
        return P

def translate_dop(dop,t):
#Require a differential_operator dop and a real t
#Return dop(x+t)
    Rx.<x> = QQ['x']
    A.<Dx> = OreAlgebra(Rx, 'Dx')
    coeff=dop.coefficients()
    exp=dop.exponents()
    dop2=0
    for i in range(len(coeff)):
        dop2+=translate_pol(coeff[i],t)*(Dx^exp[i])
    return dop2

############################Work over RBF#######################################
def maj_rb(r_b):
#Require an element in RBF
#Return a real r such that r_b<r
    return r_b.mid()+r_b.rad()
def abs_pol(pol,l):
#Require a polynom pol, a lenght l
#Return a majorant of this polynom
    x=QQ['x'].gen()
    p=0
    for i in range(l):
        p+=abs(pol[i])*x^i
    return p

def maj_rb_pol(pol,degree):
#Require a polynom pol in RBF["x"] pol, of degree degree
#Return a polynom P in QQ["x"] such that P is a majorant of pol
    x=QQ['x'].gen()
    P=0
    for i in range(degree):
        P+=(abs(pol[i].mid())+pol[i].rad())*x^i
    return P

def separation(RBF_list):
#Require the list [[Ao+/-epso],...[An+/-epsn]]
#return [Ao,...,An],[RBF(epso),...,RBF(epsn)]
    mid=[]
    rad=[]
    for r_b in RBF_list:
        mid.append(r_b.mid())
        rad.append(RBF(0).add_error(r_b.rad()))
    return mid,rad


def truncation(pol,h,n):
#Require pol=bn*x^(n-1)+...+bo, h, n the degree of the polynom
#Return  bo+...+bh-1*x^(h-1), bh*x^h+...+bn*x^n
    coeff=pol.coefficients()
    exp=pol.exponents()
    r1=0
    r2=0
    x=QQ['x'].gen()
    for i in range (n):
        if i<h:
            r1+=pol[i]*x^i
        else:
            r2+=pol[i]*x^i
    return r1,r2

################################################################################
#In this section are the main functions to get  a majorant serie
################################################################################

def power_serie_sol(dop,ini,order,n):
#Require dop, ini, order, n
#Return the Taylor expansion of the solution of dop,ini at order n
    PSS=dop.power_series_solutions(n)
    s=0
    for i in range(order):
        s+=ini[i]*PSS[order-1-i]
    return s

def res_pol(pol,order,n):
#Require pol: the Taylor expansion to order n, order the order of dop
#Return the required list of coefficients to use normalized_residual
    coeff=pol.coefficients()
    res=[]
    for i in range(order):
        res.append([abs(pol[n-1-i])])
    return res


def res(dop,ini,order,n):
#Require dop,ini,order,n
#Return the required list of coefficients [[f^(n)(0)/n!],...,[f^(n-order)(0)/(n-order)!]]
#corresponding with dop, ini to usenormalized_residual
    PSS=power_serie_sol(dop,ini,n,order)
    return res_pol(PSS,order,n)

def majorant_rest(dop,order,n,PSS):
#Require dop,order,PSS the power serie solution to the order n ,n the order where we want
#to truncate the solution
#Return a Majorant function on the residu at order n of the serie solution of dop,in
    maj=DiffOpBound(dop,max_effort=2)
    return maj.tail_majorant(n,[maj.normalized_residual(n,res_pol(PSS,order,n))])

#####################The most useful function of this section ##################


r"""
_Majorant_(n,k,dop,ini,order,x,eps),
Let set f a Solution to the "order" ordinary differential equation "dop"
with initial conditions "ini" , this function return the following terms:
f(x)t+...+(f^(n-1)(x)/k!)t^(n-1),|f^(n)(x)/n!|t^(n-1)+...+|f^(n+k)(x)/n+k!|t^(n+k),
eps((1-t^(n+k+1))/(1-t)),M^(n+k+1)(f),x)(t),M^(n+k+1)(eps(x^(n+k+1)/(1-x))(t)
M^(k)(f)(t) is a majorant fonction on the residual
example:
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

def _Majorant_(n,k,dop1,ini,order,seq_rec_order,a):
    if x==0: #check if ini in QQ^order
        dop=dop1
        PSS_ini=power_serie_sol(dop,ini,order,n+k)
        M_nk_ini=majorant_rest(dop,seq_rec_order,n+k,PSS_ini)
        left_ini,right_ini=truncation(PSS_ini,n,n+k)
        return left_ini,abs_pol(right_ini,n+k),0,M_nk_ini,0
    else: #If ini are in RBF
        dop=translate_dop(dop1,a)
        new_ini,new_eps=separation(ini)
        PSS_new_ini=power_serie_sol(dop,new_ini,order,n+k)
        PSS_new_eps=power_serie_sol(dop,new_eps,order,n+k)
        M_nk_ini=majorant_rest(dop,seq_rec_order,n+k,PSS_new_ini)
        M_nk_eps=majorant_rest(dop,seq_rec_order,n+k,PSS_new_eps)
        left_ini,right_ini=truncation(PSS_new_ini,n,n+k)
        return left_ini,abs_pol(right_ini,n+k),maj_rb_pol(PSS_new_eps,n+k),M_nk_ini,M_nk_eps


def evaluate(left_ini,right_ini,PSS_new_eps,M_nk_ini,M_nk_eps,n,t,x):
#Require _Majorant_(n,k,dop,ini,order,x,eps),n,t,x
#Return the evaluation of the function M introduced in the internship report (*) at t
    if x==0:
        if n==1:
            return sign(left_ini)*left_ini-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))
        else:
            return abs(left_ini(t))-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))
    else:
        if n==1:
            return sign(left_ini)*left_ini-PSS_new_eps(t)-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))-maj_rb(M_nk_eps.bound(RBF(t)))
        else:
            return abs(left_ini(t))-PSS_new_eps(t)-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))-maj_rb(M_nk_eps.bound(RBF(t)))


################################################################################
# Mains Algorithms
################################################################################
r"""
This function take as parameters k the order we want to expand the precision of
the majorant serie, a segment [a,b], and the precision prec we want to have.
it return intervals contained in [a,b] such that there is maybe a zero in
these intervals and such that the lenght of these interval is smaller than prec
"""
def bisection_exclusion(k,dop,ini,order,seq_rec_order,segment,prec):
    a,b=segment[0],segment[1]
    m=(a+b)/2
    d=(b-a)
    if d<prec:
        return [segment]
 #The following section is to fixe epsilon and to assure there is infinite loop
    else:
        eps=1e-8*prec
        new_ini=translate_ini(dop,ini,order,m,eps)
        if not Fixe_eps(new_ini,dop,ini,order,0,m,eps):
            return bisection_exclusion(k,dop,ini,order,seq_rec_order,[a,m-(prec/3)],prec)+bisection_exclusion(k,dop,ini,order,seq_rec_order,[m-(prec/3),m+(prec/3)],prec)+ bisection_exclusion(k,dop,ini,order,seq_rec_order,[m-(prec/3),b],prec)
        else:#epsilon fixed
            left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(1,k,dop,new_ini,order,seq_rec_order,m)
            def M(t):
                return evaluate(left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps,1,t,m)
            d/=2
            loop=0
            while M(d)<0:
                d/=2
                loop+=1
            if d==(b-a)/2:
                return []
            else:
                return bisection_exclusion(k,dop,ini,order,seq_rec_order,[a,m-d],prec)+bisection_exclusion(k,dop,ini,order,seq_rec_order,[m+d,b],prec)

r"""
increasing(f,x,eps): (fonction R->R,x in R)
Vérifie que la fonction est croissante sur l'intervalle [x,x+epsilon]
"""
def increasing(f,x,eps):
#Require function, real x, eps
#Return True if f is increasing False otherwise
    return (f(x+eps)-f(x))>0

################These functions aim to deal with the eps condition##############
def ini_are_good(ini,i):
#Require ini, i, j
#Check if the initial conditions f^(i)/i!,...,f^(j-1)/(j-1)! could be use
    return (abs(ini[i].mid())-ini[i].rad())>1e4*ini[i].rad()

def Fixe_eps(new_ini,dop,ini,order,i,x,eps):
#Require dop,ini int i,j
#Check if the coefficients ini[i],..., ini[j-1] are good to manipulate it returns
#a boolean and change the new_ini that it can can be use without any trouble.
    if x==0:
        if ini[0]==0:
            return False
        else:
            eps=sign(ini[0])*1e-8*ini[0]
            new_ini=new_ini=translate_ini(dop,ini,order,x,eps)
    else:
        count=0
        while not ini_are_good(new_ini,i) and count<5:
            eps*=1e-10
            new_ini=translate_ini(dop,ini,order,x,eps)
            count+=1
        if count==5:
            return False
        else:
            return True

################################################################################

#################This functions aims to certificate the zeros##################
#This function tries to certificate a zero in a segment using theorems
#in the internship rapport

def certified_zero(dop,ini,order,seq_rec_order,x,prec):
#Require dop, ini, order, x, prec
#Return [0,0] if it can not certified a zero in an interval
#Return [a,s] the maximum and the minimum reals such that [x-s,x+s] and
#[x-a,x+a] contains a single zero
    eps=1e-5*prec
    new_ini=translate_ini(dop,ini,order,x,eps)
    #The following section is to fixe epsilon
    if Fixe_eps(new_ini,dop,ini,order,1,x,eps):
        dop1=translate_dop(dop,x)
        left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(2,10,dop1,new_ini,order,seq_rec_order,x)
        left_eps,right_eps=truncation(PSS_new_eps,2,PSS_new_eps.degree())
        f0=sign(left_ini[0])*left_ini[0]+left_eps[0]
        f1=sign(left_ini[1])*left_ini[1]-left_eps[1]
        def f(t):
            return f1*t-right_ini(t)-right_eps(t)-maj_rb(M_1k_ini.bound(RBF(t)))-maj_rb(M_1k_eps.bound(RBF(t)))-f0
        a=f0/f1
        b=max(16*a,2560*prec)
        while b-a>3*prec and f(a)<=0 and f(b)<=0:
            m=(a+b)/2
            if increasing(f,m,eps):
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
    else:
        return [0,0]


###########################The main function####################################
def find_certified_zeros(dop,ini,segment,iteration=0,max_iteration=3):
#Require dop, ini, segment on wich we want to certificate the zeros
#Return the list of segments determinated and the segments still indeterminated
#The user can improve max iteration there are still some segments which are unknown
    order=len(ini)
    seq_rec_order=recc_order(dop)
    k=5+seq_rec_order
    if segment==[]:
        return [[],[]]
    if iteration>max_iteration:#This is to avoid infinite loop
        return [[],segment]
    else:
        a,b=segment[0],segment[1]
        prec=min(1e-4*(b-a),1e-1)
        indeterminated=bisection_exclusion(k,dop,ini,order,seq_rec_order,segment,prec)
        n=len(indeterminated)
        determinated=[False for k in range(n)]
        big_admitted=[]
        small_admitted=[]
        for i in range(n):
            x=indeterminated[i][1]
            l=certified_zero(dop,ini,order,seq_rec_order,x,prec)
            if l[0]>0:
                big_admitted.append([x-l[0],x+l[0]])
                small_admitted.append([x-l[1],x+l[1]])
        still_indeterminate=still_indeterminated(big_admitted,indeterminated,determinated)
        admitte=admitted(small_admitted)
        if still_indeterminate==[]:
            return [admitte,[]]
        else:
            unsure=[[]]
            for i in range(len(still_indeterminated)):
                admitte,unsure=concatenate([admitte,unsure],find_certified_zeros(dop,ini,still_indeterminated[i],iteration+1,max_iteration))
            if unsure!=[[]]:
                print("possibly a zero of multiplicity superior at 1 in the second list, you can increase max_iteration")
                print("or test certified_zero_multiplicity(dop,ini,x,prec,m) to test how many zeros there are possibly")
                print("in the intervals still indeterminated")
        return [admitte,unsure]

def concatenate(sol1,sol2):
#Require sol1 and sol2 of the form [admitted,unsure] where admitted if the list
#of certified_zero of f solution of dop,ini, and unsure the list of uncertified
#segments
#Return one list of the form [admitted,unsure]
    return (sol1[0]+sol2[0]),(sol1[1]+sol2[1])

def admitted(small_admitted):
#Require the list of segments containing only one zero
#Return the disjoint list of segments containing only one zero
    if small_admitted==[]:
        return []
    n=len(small_admitted)
    admit=[]
    segment=small_admitted[0]
    i=1
    while i<n:
        intersect=intersection(segment,small_admitted[i])
        if intersect!=[]:
            segment=intersect
            i+=2
        else:
            admit.append(segment)
            segment=small_admitted[i]
    admit.append(segment)
    return admit

def test_disjoint(segm_list):
#Require segm_list a list of segments ordered in increasing bounds
#Return if the list is disjoint or not
    for i in range(len(admis)-1):
        if admis[i][1]>admis[i][0]:
            return False
    return True

def intersection(segment1,segment2):
#Require segment1 and segment2 that are ordered in increasing order
#Return the intersection of segment1 and segment2
    if segment1[1]<segment2[0] or segment2[1]<segment1[0]:
        return []
    else:
        return [max(segment1[0],segment2[0]),min(segment1[1],segment2[1])]

def still_indeterminated(big_admitted,indeterminated,determinated):
#Require the list of segment containing one zero, the list of indeterminated
#segments and the list of boolean wich have the same lenght as indeterminated
#Return a list of indeterminated segments after check that indeterminated
#segments are not in the determinated (big_admitted) segments
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
#Require 2 segments
#Return if segment1 is included in segment2
    if segment1==[]:
        return True
    if segment2==[]:
        return False
    else:
        return (segment1[1]<=segment2[1])and(segment2[0]<=segment1[0])


def plot_function(dop,ini,name,color_fun,segment):
    a=segment[0]
    b=segment[1]
    n=(b-a)*1e2//1
    x=[b+k*1e-2 for k in range(n)]
    y=[]
    for k in range (n):
        y.append(dop.numerical_solution(ini,[0,b+k*1e-2],1e-10).mid())
    plt.plot(x,y,color=color_fun,label=name)
    plt.legend()
    plt.show()
