
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

def _Majorant_(n,k,dop,ini,order,x,eps):
    if x==0: #check if ini in QQ^order
        PSS_ini=power_serie_sol(dop,ini,order,n+k)
        M_nk_ini=majorant_rest(dop,order,n+k,PSS_ini)
        left_ini,right_ini=truncation(PSS_ini,n,n+k)
        return left_ini,abs_pol(right_ini,n+k),0,M_nk_ini,0
    else: #If ini are in RBF
        new_ini,new_eps=separation(ini)
        PSS_new_ini=power_serie_sol(dop,new_ini,order,n+k)
        PSS_new_eps=power_serie_sol(dop,new_eps,order,n+k)
        M_nk_ini=majorant_rest(dop,order,n+k,PSS_new_ini)
        M_nk_eps=majorant_rest(dop,order,n+k,PSS_new_eps)
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
            return sign(left_ini)*left_ini-maj_rb(PSS_new_eps(t))-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))-maj_rb(M_nk_eps.bound(RBF(t)))
        else:
            return abs(left_ini(t))-maj_rb(PSS_new_eps(t))-right_ini(t)-maj_rb(M_nk_ini.bound(RBF(t)))-maj_rb(M_nk_eps.bound(RBF(t)))


################################################################################
# Mains Algorithms
################################################################################
r"""
This function take as parameters k the order we want to expand the precision of
the majorant serie, a segment [a,b], and the precision prec we want to have.
it return intervals contained in [a,b] such that there is maybe a zero in
these intervals and such that the lenght of these interval is smaller than prec
"""
def bisection_exclusion(k,dop,ini,order,segment,prec):
    a,b=segment[0],segment[1]
    m=(a+b)/2
    d=(b-a)
    eps=1e-5*prec
    new_ini=translate_ini(dop,ini,order,m,eps)
    if d<prec:
        return [segment]
    else: #The following section is to fixe epsilon
        if m!=0:
            count=0
            while not ini_are_good(new_ini,0,1) and count<10:
                eps*=1e-8
                new_ini=translate_ini(dop,ini,order,m,eps)
            if count==10: #suspection that f(m)==0
                return bisection_exclusion(k,dop,ini,order,[a,m-10*eps],prec)+bisection_exclusion(k,dop,ini,order,[m-10*eps,m+5*eps],prec)+ bisection_exclusion(k,dop,ini,order,[m+5*eps,b],prec)
        #epsilon fixed

        left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(1,k,dop,new_ini,order,m,eps)
        print("PSS_new_eps",PSS_new_eps)
        def M(t):
            return evaluate(left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps,1,t,m)
        d/=2
        while M(d)<0:
            d/=2
            print(d)
        if d==(b-a)/2:
            return []
        else:
            return bisection_exclusion(k,dop,ini,order,[a,m-d],prec)+bisection_exclusion(k,dop,ini,order,[m+d,b],prec)

r"""
increasing(f,x,eps): (fonction R->R,x in R)
Vérifie que la fonction est croissante sur l'intervalle [x,x+epsilon]
"""
def increasing(f,x,eps):
#Require function, real x, eps
#Return True if f is increasing False otherwise
    return (f(x+eps)-f(x))>0

################These functions aim to deal with the eps condition##############
def ini_are_good(ini,i,j):
#Require ini, i, j
#Check if the initial conditions f^(i)/i!,...,f^(j-1)/(j-1)! could be use
    for k in range (i,j):
        if (ini[k].mid()-ini[k].rad())<1e4*ini[k].rad():
            return False
    return True

def ini_non_null(ini,i,j):
#require ini, i, j
#Check if the initial conditions f^(i)/i!,...,f^(j)/j! are all non null
    for i in range(i,j):
        if ini[k]==0:
            return False
    return True
################################################################################

#################This functions aims to certificate the zeros##################
#This function tries to certificate a zero in a segment using theorems
#in the internship rapport

def certified_zero(dop,ini,order,x,prec):
#Require dop, ini, order, x, prec
#Return [0,0] if it can not certified a zero in an interval
#Return [a,s] the maximum and the minimum reals such that [x-s,x+s] and
#[x-a,x+a] contains a single zero
    eps=1e-5*prec
    new_ini=translate_ini(dop,ini,order,x,eps)
    #The following section is to fixe epsilon
    if ini_non_null(new_ini,0,2):
        count=0
        while not ini_are_good(translate_ini,0,2) and count<10:
            eps*=1e-8
            new_ini=translate_ini(dop,ini,order,x,eps)
        left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(2,10,dop,ini,order,x,eps)
        left_eps,right_eps=truncation(PSS_new_eps,2,PSS_new_eps.degree())
        f0=sign(left_ini[0])*left_ini[0]+left_eps[0]
        f1=sign(left_ini[1])*left_ini[1]-left_eps[1]
        def f(t):
            return f1*t-right_eps(t)-maj_rb(M_1k_ini.bound(RBF(t)))-maj_rb(M_1k_eps.bound(RBF(t)))-f0
        a=f0/f1
        b=max(16*a,256*prec)
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
def find_certified_zeros(dop,ini,segment,iteration=0,max_iteration=10):
#Fonction renvoyant la liste des zéros sous forme de liste de segment ou de real
#ball si ces zéros sont simples, sinon renvoie la liste des zéros certifiés
# et la liste des zéros de multiplicité supérieure
    order=len(ini)
    k=10
    if segment==[]:
        return [[],[]]
    if iteration>max_iteration:#This is to avoid infinite loop
        return [[],segment]
    else:
        a,b=segment[0],segment[1]
        prec=min(1e-3*(b-a),1e-1)
        indeterminated=bisection_exclusion(k,dop,ini,order,segment,prec)
        n=len(indeterminated)
        determinated=[False for k in range(n)]
        big_admitted=[]
        small_admitted=[]
        for i in range(n):
            x=indeterminated[i][1]
            l=certified_zero(dop,ini,order,x,prec)
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
    return admitted

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
    if segment1[1]<segment2[0]:
        return []
    else:
        return [segment2[0],segment1[1]]

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


def plot_D_finite_function(dop,ini,f,eps,a,b):
#Function qui plotting f and M(f,x) in the interval [a,b]
    x=(a+b)/2
    left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps=_Majorant_(1,k,dop,ini,x,eps)
    def M(t):
        return evaluate(left_ini,right_ini,PSS_new_eps,M_1k_ini,M_1k_eps,t,1,x)
    P1=plot(M(t),(t,a,b))
    P2=plot(f(t),(t,a,b))
    show(p1+p2)
