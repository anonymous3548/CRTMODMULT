import qiskit
from qiskit import QuantumRegister, ClassicalRegister, QuantumCircuit, assemble, Aer
from qiskit.circuit.library import Permutation
from qiskit.quantum_info import Statevector,Operator
from qiskit.visualization import plot_histogram
import numpy as np
import copy



#multiply all list elements
def mul(a):
    tmp=a[0]
    for i in range(1,len(a)):
        tmp=tmp*a[i]
    return tmp

#li : list of irreducible polynomials, i:index. generate matrix corresponding to h_i(x) mod f
def gen_mat(li,i,f,Rf):
    tp=li[i]
    ttt=f/tp
    R0=S.quotient(tp)
    ab=Rf(ttt)*Rf(R0(ttt)^-1)
    return matrix([Rf(ab*t^j).list() for j in range(0,tp.degree())]).transpose()


#element wise addition for list
def element_add(M,N):
    return [k(M[i]+ N[i]) for i in range(len(M))]


#CNOT gate cost of out_mult_reuse 행렬 곱셈 구현 비용(재활용으로) - unitvector는 항상 보유하고, 만들어야 할 vector를 기존 벡터 이용해서 outplace로 만듦
#1개로 만들 수 있는 것부터 우선적으로 만들고, 2개를 다음에... 이렇게 간다.
#unit vector를 안 쓰고 더해서 새로운 것이 만들어질 수 있는데 그건 고려 안 한다.
def calc_cost(N):
    order=[]
    len_col=N.ncols()
    
    tmp2=tuple([k(0)]*len_col)
    current_set=set()
    
    #base 상태 - unit vector
    for i in range(len_col):
        de=[k(0)]*len_col
        de[i]=k(1)
        current_set.add(tuple(de))

    #만들어야 할 벡터
    ts=[tuple(i) for i in N.rows()]
    
    #0 vector 제거
    while tmp2 in ts:
        ts.remove(tmp2)

        
    #unit vector 제거        
    row_set=set(ts)
    row_set=row_set-current_set
    
    
    #중복 벡터 비용 : 벡터 당 1            
    cost=len(ts)-len(row_set)
    
    while row_set!=set():
        dic={}
        for i in row_set:
            for j in current_set:
                tmp=element_add(i,j).count(1)
                dic[(i,j)]=tmp
                if tmp==1:
                    current_set.add(i)
                    row_set.remove(i)
                    order.append(i)
                    cost=cost+2
                    break
            if tmp==1:
                break
        if tmp!=1:
            ww=min(dic,key=dic.get)[0]
            current_set.add(ww)
            row_set.remove(ww)
            order.append(ww)
            cost=cost+tmp+1
    return cost, order



#x-inf 항
def gen_inf_mat(n,f):
    tmp=[]
    for j in range(f.degree(),f.degree()+n):
        Ri=S.quotient(f)
        tmp.append(Ri(t^j).list())
    return matrix(tmp).transpose()

#mod i(x) 에 대한 reduction : i+1차~n차
def gen_redc_mat(i,n):
    tmp=[]
    for j in range(i.degree(),n):
        Ri=S.quotient(i)
        tmp.append(Ri(t^j).list())
    return matrix(tmp)



#크기가 1 차이날 때, b의 row, a의 column에 0을 추가해서 크기를 맞춘다.
def tmpadd(a,b):
    if a.nrows()==b.nrows():
        return a+b
    elif a.nrows()>b.nrows():
        
        L=b.rows()
        L[0:0]=[[0]*b.ncols()]
        
        M=a.columns()
        M[a.ncols():a.ncols()]=[[0]*a.nrows()]
        return matrix(L)+matrix(M).transpose()
    else:
        return tmpadd(b,a)


#for mxn matrix M, randomly select n linearly independent rows of M
def select_indp(M):
    N=matrix(k,M.ncols())
    while(1):
        tmp=[]
        for i in range(M.ncols()):
            t=randrange(M.nrows())
            tmp.append(t)
            N[i]=M[t]
        if(N.rank()==M.ncols()):
            break
    return N,M[   [ k for k in range(M.nrows()) if k not in tmp]],tmp



def order_poly(N):
    tmp=[]
    tp={}
    for i in range(1,len(N)):
        tp[i]=[(i+1)*N[i][1],-i]
    sorted_tp = dict(sorted(tp.items(), key = lambda item: item[1])).keys()
    flag=0
    for i in sorted_tp:
        if tp[i][0]>=N[0][1] and flag==0:
            flag=1
            tmp.append(irr_list[0][1]^N[0][1])
        for j in range(N[i][0]):
            tmp.append(irr_list[i][j]^N[i][1])
    tmp.insert(0, irr_list[0][0]^N[0][0] )
    return tmp


#add identity matrix to M
def add_idt(M):
    nn=M.ncols()
    N=identity_matrix(nn)
    return matrix(M.rows()+N.rows())


def XOR(qr,qc,idx):
    for i in idx:
        qc.cx(qr[int(i[0])],qr[int(i[1])])


def make_operation(T,term):
    tmpT=copy.deepcopy(T)
    
    M=[]
    N=[]
    for i in range(len(term[0])):
        if {i+1} in tmpT:
            M.append([[],i,T.index({i+1})])
            tmpT.remove({i+1})
    
    for i in range(len(term)-1):
        ind1=0
        ind2=0
        for j in range(len(term[0])):
            if term[i][j]!=term[i+1][j]:
                ind1=j

        for j in range(len(term[0])):
            if term[i+1][ind1]==(term[i][ind1]|term[i][j]) - (term[i][ind1]&term[i][j]):
                ind2=j
                N.append([ind2,ind1])
                
        if term[i+1][ind1] in tmpT:
            ww=T.index(term[i+1][ind1])
            M.append([N,ind1,ww])
            tmpT.remove(term[i+1][ind1])
            N=[]
    M.append(N)
    return M


def R_redc(M,f):
    tx=M.transpose()
    RR=S.quotient(f,t)
    tmp=[]
    for i in range(tx.nrows()):
        tmp.append(   RR(tx[i].list()).list()    )
        
    return matrix(tmp).transpose()


#generate list of irreducible polynomials of degree n
def irr_poly(n):
    myfactors = [ f for f, multiplicity in (t^(2^n)-t).factor() if f.degree() == n ]
    return myfactors



#d : 전체 차수(입력)
#m_list : 다항식 리스트
#l : 다항식 인덱스
#dif : 연속한 reduction에서 크기가 다를 때

def mod_reduction_start(l,d,m_list):
    qr = QuantumRegister(d)
    qc = QuantumCircuit(qr)
    
    
    M=gen_redc_mat(m_list[l],d)    
    i=0
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            if M[i][j]==1:
                qc.cx(qr[int(i)+M.ncols()],qr[int(j)])   
    return qc              
                

                
def mod_reduction(l,d,m_list):
    
    qr = QuantumRegister(d)
    qc = QuantumCircuit(qr)    
    
    M1=gen_redc_mat(m_list[l],d)
    M2=gen_redc_mat(m_list[l+1],d)
    
    if M1.nrows()==M2.nrows():
        M=M1+M2
        i=0
        for i in range(M.nrows()):
            for j in range(M.ncols()):
                if M[i][j]==1:
                    qc.cx(qr[int(i)+M.ncols()],qr[int(j)])                

    elif M2.nrows()<M1.nrows():

        for j in range(M1.ncols()):
            if M1[0][j]==1:
                qc.cx(qr[M1.ncols()],qr[int(j)])        
        M=tmpadd(M2,M1)
        for i in range(1,M.nrows()):
            for j in range(M.ncols()):
                if M[i][j]==1:
                    qc.cx(qr[int(i-1)+M.ncols()],qr[int(j)])        
    return qc








def out_place(M):
    qr=QuantumRegister(M.nrows()+M.ncols())
    qc=QuantumCircuit(qr)
    
    #순서 저장
    order=calc_cost(M)[1]

    tmp=[tuple(i) for i in M.rows()]
    
    order_tmp_list={}
    
    
    #unit vector 그냥 CNOT
    for i in range(M.nrows()):
        if tmp[i].count(1)==1:
            for j in range(len(tmp[i])):
                if tmp[i][j]==1:
                    qc.cx(qr[int(j)],qr[int(i+M.ncols())])
  
    #그 외의 것에 대하여 순서대로
    for i in range(len(order)):
        for j in range(M.nrows()):
            if tmp[j]==order[i]:
                dic={}
                dic[-1]=5000
                for w in range(i):
                #만들어야 할 것 탐색
                    tmpp=element_add(order[i],order[w]).count(1)
                    dic[(i,w)]=tmpp                
                ww=min(dic,key=dic.get)
                
                #이전에 만든 값을 사용하지 않을 때
                if tmp[j].count(1)<dic[ww]+1:
                    for t in range(len(tmp[j])):
                        if tmp[j][t]==1:
                            qc.cx(qr[int(t)],qr[int(j+M.ncols())])
                        
                    order_tmp_list[i]=j

                        
                #이전에 만든 값을 사용할 때
                else:
                    xx=element_add(order[i],order[ww[1]])
                    
                    qc.cx(qr[int(order_tmp_list[ww[1]]+M.ncols())],qr[int(j+M.ncols())])
                    
                    for t in range(len(xx)):
                        if xx[t]==1:
                            qc.cx(qr[int(t)],qr[int(j+M.ncols())])   
                    order_tmp_list[i]=j
                
                break
    
    k = GF(2)               
    len_col=M.ncols()    
    tmp2=tuple(  [k(0)]*len_col   )
    current_set=set()
    
    #unit vector 집합 생성
    for i in range(len_col):
        de=[k(0)]*len_col
        de[i]=k(1)
        current_set.add(tuple(de))
    
    #0 vector 제거
    ts=copy.deepcopy(tmp)
    while tmp2 in ts:
        ts.remove(tmp2)

    #unit vector 제거        
    row_set=set(ts)
    row_set=row_set-current_set
                    

    #row_set : 2개 이상 XOR 되어 있는 집합
    #위에 알고리즘 상 무조건 처음 있는 것부터 만들어지고, 나머지는 순서대로 복사하면 됨
    for i in row_set:
        for j in range(len(tmp)):
            if tmp[j]==i:
                for w in range(j+1,len(tmp)):
                    if tmp[w]==i:
                        qc.cx(qr[int(j+M.ncols())],qr[int(w+M.ncols())])
                break       
    return qc









def in_place(P,L,U):
    d=U.nrows()
    qr=QuantumRegister(d)
    qc=QuantumCircuit(qr)
    tmpP=copy.deepcopy(P)    
    
    for i in range(d):
        for j in range(i+1,d):
            if U[i][j]==1:
                qc.cx(qr[int(j)],qr[int(i)])
                                
    for i in reversed(range(d)):
        for j in reversed(range(i)):
            if L[i][j]==1:
                qc.cx(qr[int(j)],qr[int(i)])
                
    Perm=Permutation(d,[np.where(np.array(P[k])==1)[0][0] for k in range(d)])        
    sub_inst = Perm.to_instruction()
    qc.append(sub_inst,[qr[j] for j in range(d)])
                
    return qc



def R_left(qr,qc,X):
    Xprime=np.array(X)
    wher=np.where(Xprime==1)[0].tolist()
    if(len(wher)==2):
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])
        
    if(len(wher)==3):
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])        

    if(len(wher)==4):  
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])         
        
    if(len(wher)==5):
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])                 
        
    if(len(wher)==6):
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])         
        
    if(len(wher)==7):
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])           
        
        
    if(len(wher)==8):
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])
        
        
    if(len(wher)==9):
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])        
        
        
    if(len(wher)==10):
        qc.cx(qr[int(wher[1])],qr[int(wher[9])])
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])        
        
    if(len(wher)==11):
        qc.cx(qr[int(wher[2])],qr[int(wher[10])])
        qc.cx(qr[int(wher[1])],qr[int(wher[9])])
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])         
        
    if(len(wher)==12):
        qc.cx(qr[int(wher[3])],qr[int(wher[11])])
        qc.cx(qr[int(wher[2])],qr[int(wher[10])])
        qc.cx(qr[int(wher[1])],qr[int(wher[9])])
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])           
        
        
    if(len(wher)==13):
        qc.cx(qr[int(wher[4])],qr[int(wher[12])])
        qc.cx(qr[int(wher[3])],qr[int(wher[11])])
        qc.cx(qr[int(wher[2])],qr[int(wher[10])])
        qc.cx(qr[int(wher[1])],qr[int(wher[9])])
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])        
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])
        
    return wher


def R_right(qr,qc,X):

    Xprime=np.array(X)
    wher=np.where(Xprime==1)[0].tolist()

    if(len(wher)>=2):
        qc.cx(qr[int(wher[0])],qr[int(wher[1])])
    if(len(wher)>=3):
        qc.cx(qr[int(wher[1])],qr[int(wher[2])])
    if(len(wher)>=4):
        qc.cx(qr[int(wher[0])],qr[int(wher[3])])
        
        
    if(len(wher)>=5):
        qc.cx(qr[int(wher[0])],qr[int(wher[4])])          
    if(len(wher)>=6):
        qc.cx(qr[int(wher[1])],qr[int(wher[5])])           
    if(len(wher)>=7):
        qc.cx(qr[int(wher[2])],qr[int(wher[6])])           
    if(len(wher)>=8):
        qc.cx(qr[int(wher[3])],qr[int(wher[7])])

        
        
    if(len(wher)>=9):
        qc.cx(qr[int(wher[0])],qr[int(wher[8])])          
    if(len(wher)>=10):
        qc.cx(qr[int(wher[1])],qr[int(wher[9])])           
    if(len(wher)>=11):
        qc.cx(qr[int(wher[2])],qr[int(wher[10])])           
    if(len(wher)>=12):
        qc.cx(qr[int(wher[3])],qr[int(wher[11])])        
    if(len(wher)>=13):
        qc.cx(qr[int(wher[4])],qr[int(wher[12])])          
    if(len(wher)>=14):
        qc.cx(qr[int(wher[5])],qr[int(wher[13])])           
    if(len(wher)>=15):
        qc.cx(qr[int(wher[6])],qr[int(wher[14])])           
    if(len(wher)>=16):
        qc.cx(qr[int(wher[7])],qr[int(wher[15])])


#SBF(T, R)
def SBF_TR(T,R,n):
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(R.nrows())
    qc = QuantumCircuit(A,B,C)
    
    k=0
    for i in range(R.ncols()):
        XOR(A,qc,T[i][0])
        XOR(B,qc,T[i][0])
        
        k=R_left(C,qc,R.transpose()[T[i][2]])
        
        if len(k)>0:
            qc.ccx(A[int(T[i][1])],B[int(T[i][1])],C[int(k[0])])
                
        R_right(C,qc,R.transpose()[T[i][2]])
    XOR(A,qc,T[R.ncols()])
    XOR(B,qc,T[R.ncols()])
    
    return qc



def inf_mul(n):
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(n)
    qc = QuantumCircuit(A,B,C)
    

    for i in range(n):
        if i>0:
            qc.cx(C[int(i)],C[int(i-1)])    
    
    for i in range(n-1,-1,-1):
        qc.ccx(A[int(i)],B[int(i)],C[int(i)])
        if i>0:
            qc.cx(C[int(i)],C[int(i-1)])
    for i in range(1,n):
        for j in range(i):
            if j<i-j :
                qc.cx(A[int(n-1-i+j)],A[int(n-1-j)])
                qc.cx(B[int(n-1-i+j)],B[int(n-1-j)])
                qc.ccx(A[int(n-1-j)],B[int(n-1-j)],C[int(n-1-i)])
                qc.cx(A[int(n-1-i+j)],A[int(n-1-j)])
                qc.cx(B[int(n-1-i+j)],B[int(n-1-j)])
    return qc






def CRTMODMULT(m_x_list,n,p_x):
    
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(n)
    qc = QuantumCircuit(A,B,C)
    
    m_list=order_poly(m_x_list)
    l=len(m_list)
    m=mul(m_list)
    w=2*n-1-m.degree()
    Rf=S.quotient(m,t)

    for i in range(l):
        tmp3=gen_mat(m_list,i,m,Rf)
        tmp3=R_redc(tmp3,p_x)
                
        abcde = select_indp(tmp3)
        
        ##permutation
        Perm=Permutation(n,abcde[2]+[k for k in range(n) if k not in abcde[2]])
        sub_inst = Perm.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
       
        #qc.barrier()
        
        ##inverse
        P,L,U=(abcde[0]).LU()
        in_op=in_place(P,L,U)
        in_op_2=copy.deepcopy(in_op)
        sub_inst = in_op.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(P.nrows())])
        
        #qc.barrier()
        
        out_op = out_place(abcde[1])
        out_op_2=copy.deepcopy(out_op)        
        sub_inst = out_op.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
        
        #qc.barrier()
        
        #T,R 지정
        deg=m_list[i].degree()
        
        if deg>8:
            sub_inst =CRTMODMULT([[2,2],[1,1],[2,1],[1,1]],deg,m_list[i]).decompose().to_instruction()
            qc.append(sub_inst,  [A[j] for j in range(deg)]+[B[j] for j in range(deg)]+[C[j] for j in range(deg)]  )          
        else:
            T=KLF_order[deg]
            R=R_redc(r[deg],m_list[i])
            sub_inst = SBF_TR(T,R,deg).to_instruction()
            qc.append(sub_inst,  [A[j] for j in range(deg)]+[B[j] for j in range(deg)]+[C[j] for j in range(R.nrows())]  )          
        
        #qc.barrier()
        
        
        ##정방향    
        sub_inst = out_op_2.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
        
        #qc.barrier()
        
        sub_inst = in_op_2.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(P.nrows())])            
        
        #qc.barrier()
        
        ##permutation
        Perm=Permutation(n,abcde[2]+[k for k in range(n) if k not in abcde[2]])
        sub_inst = Perm.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
        P,L,U=(abcde[0]).LU()
        
        #qc.barrier()
        
        if i==0:
            #처음 mod reduction
            sub_inst = mod_reduction_start(1,n,m_list).to_instruction()
        elif i==l-1:
            #끝 mod reduction
            sub_inst = mod_reduction_start(l-1,n,m_list).to_instruction()
        else:
            #mod reduction 두개 합친 것            
            sub_inst = mod_reduction(i,n,m_list).to_instruction()

        qc.append(sub_inst,  [A[j] for j in range(n)]  )
        qc.append(sub_inst,  [B[j] for j in range(n)]  )
        
    #inf 항


    if w>0:
        tmp3=gen_inf_mat(w,m)
        tmp3=add_idt(tmp3)
        tmp3=R_redc(tmp3,p_x)
        abcde = select_indp(tmp3)

        #qc.barrier()
        
        #permutation
        Perm=Permutation(n,abcde[2]+[k for k in range(n) if k not in abcde[2]])
        sub_inst = Perm.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
        P,L,U=(abcde[0]).LU()
        
        #qc.barrier()        

        ##inverse
        in_op=in_place(P,L,U)
        in_op_2=copy.deepcopy(in_op)        
        sub_inst = in_op.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(P.nrows())])
        
        #qc.barrier()
        
        out_op = out_place(abcde[1])
        out_op_2=copy.deepcopy(out_op)
        sub_inst = out_op.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])

        #inf mul

        #qc.barrier()
        
        sub_inst = inf_mul(w).to_instruction()
        qc.append(sub_inst,  [A[j] for j in range(n-w,n)]+[B[j] for j in range(n-w,n)]+[C[j] for j in range(w)]  )       

        ##정방향
        
        #qc.barrier()
        
        sub_inst = out_op_2.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])
        
        #qc.barrier()
        
        sub_inst = in_op_2.to_instruction()
        qc.append(sub_inst,[C[j] for j in range(P.nrows())])
        
        #qc.barrier()

        #permutation
        Perm=Permutation(n,abcde[2]+[k for k in range(n) if k not in abcde[2]])        
        sub_inst = Perm.inverse().to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])

    return qc
















k = GF(2)
S.<t> = PolynomialRing(k)

#list of T matrix of Karatsuba-like Formulae
T={}
T[2]=[np.array([0,1,0]),
np.array([0,1,1]),
np.array([0,0,1])]

T[3]=[np.array([0,1 ,0, 0]),
np.array([0,0 , 1, 0]),
np.array([0,1, 1, 0]),
np.array([0,0 ,0, 1]),
np.array([0,0 ,1, 1]),
np.array([0,1 ,1, 1])]


T[4]=[np.array([0 ,1, 0, 0, 0]),
np.array([0 ,0, 1, 0, 0]),
np.array([0 ,1, 1, 0, 0]),
np.array([0 ,0, 0, 1, 0]),
np.array([0 ,1, 0, 1, 0]),
np.array([0 ,0, 0, 0, 1]),
np.array([0 ,0, 1, 0, 1]),
np.array([0 ,0, 0, 1, 1]),
np.array([0 ,1, 1, 1, 1])]

T[5]=[np.array([0, 1, 0, 0, 0, 0]),
np.array([0, 0, 1, 0, 0, 0]),
np.array([0, 1, 1, 0, 0, 0]),
np.array([0, 0, 0, 1, 0, 0]),
np.array([0, 1, 0, 1, 0, 0]),
np.array([0, 0, 0, 0, 1, 0]),
np.array([0, 1, 0, 1, 1, 0]),
np.array([0, 0, 0, 0, 0, 1]),
np.array([0, 0, 0, 1, 0, 1]),
np.array([0, 0, 1, 1, 0, 1]),
np.array([0, 0, 0, 0, 1, 1]),
np.array([0, 1, 1, 0, 1, 1]),
np.array([0, 1, 1, 1, 1, 1]),]


T[6]=[np.array([0,1, 0, 0, 0, 0, 0]),
np.array([0,0, 1, 0, 0, 0, 0]),
np.array([0,1, 1, 0, 0, 0, 0]),
np.array([0,0, 1, 1, 0, 0, 0]),
np.array([0,1, 1, 1, 0, 0, 0]),
np.array([0,0, 0, 1, 1, 0, 0]),
np.array([0,0, 0, 0, 0, 1, 0]),
np.array([0,0, 1, 0, 0, 1, 0]),
np.array([0,0, 0, 0, 1, 1, 0]),
np.array([0,1, 1, 0, 1, 1, 0]),
np.array([0,0, 0, 0, 0, 0, 1]),
np.array([0,1, 0, 1, 0, 0, 1]),
np.array([0,1, 0, 0, 1, 0, 1]),
np.array([0,1, 0, 1, 1, 0, 1]),
np.array([0,0, 0, 0, 0, 1, 1]),
np.array([0,0, 1, 1, 0, 1, 1]),
np.array([0,0, 0, 0, 1, 1, 1])]


T[7]=[np.array([0,1, 0, 0, 0, 0, 0, 0]),
np.array([0,0, 1, 0, 0, 0, 0, 0]),
np.array([0,1, 1, 0, 0, 0, 0, 0]),
np.array([0,0, 0, 1, 0, 0, 0, 0]),
np.array([0,1, 0, 1, 0, 0, 0, 0]),
np.array([0,1, 0, 1, 1, 0, 0, 0]),
np.array([0,0, 1, 1, 1, 0, 0, 0]),
np.array([0,0, 0, 1, 0, 1, 0, 0]),
np.array([0,1, 0, 1, 0, 1, 0, 0]),
np.array([0,0, 0, 0, 0, 0, 1, 0]),
np.array([0,0, 1, 0, 0, 0, 1, 0]),
np.array([0,0, 0, 0, 1, 0, 1, 0]),
np.array([0,0, 1, 0, 1, 0, 1, 0]),
np.array([0,0, 1, 1, 0, 1, 1, 0]),
np.array([0,0, 0, 0, 0, 0, 0, 1]),
np.array([0,1, 0, 1, 0, 0, 0, 1]),
np.array([0,1, 0, 1, 0, 1, 0, 1]),
np.array([0,1, 1, 0, 1, 1, 0, 1]),
np.array([0,1, 1, 1, 1, 1, 0, 1]),
np.array([0,0, 0, 0, 0, 0, 1, 1]),
np.array([0,1, 0, 1, 1, 0, 1, 1]),
np.array([0,1, 1, 1, 1, 1, 1, 1])]

T[8]=[np.array([0,1, 0, 0, 0 ,0 ,0 ,0 ,0]),
np.array([0,0, 1, 0, 0 ,0 ,0 ,0 ,0]),
np.array([0,1, 1, 0, 0 ,0 ,0 ,0 ,0]),
np.array([0,0, 0, 1, 0 ,0 ,0 ,0 ,0]),
np.array([0,1, 0, 1, 0 ,0 ,0 ,0 ,0]),
np.array([0,0, 1, 0, 1 ,1 ,1 ,0 ,0]),
np.array([0,0, 0, 0, 0 ,0 ,0 ,1 ,0]),
np.array([0,0, 1, 1, 1 ,0 ,0 ,1 ,0]),
np.array([0,0, 0, 1, 1 ,1 ,0 ,1 ,0]),
np.array([0,1, 0, 1, 0 ,0 ,1 ,1 ,0]),
np.array([0,1, 0, 1, 1 ,0 ,1 ,1 ,0]),
np.array([0,0, 1, 0, 0 ,1 ,1 ,1 ,0]),
np.array([0,0, 0, 1, 0 ,1 ,1 ,1 ,0]),
np.array([0,0, 0, 0, 0 ,0 ,0 ,0 ,1]),
np.array([0,1, 0, 1, 0 ,0 ,0 ,0 ,1]),
np.array([0,1, 1, 1, 0 ,1 ,0 ,0 ,1]),
np.array([0,1, 0, 1, 1 ,1 ,0 ,0 ,1]),
np.array([0,1, 1, 1, 0 ,0 ,1 ,0 ,1]),
np.array([0,0, 1, 1, 0 ,1 ,1 ,0 ,1]),
np.array([0,1, 0, 0, 1 ,1 ,1 ,0 ,1]),
np.array([0,0, 0, 0, 0 ,0 ,0 ,1 ,1]),
np.array([0,1, 1, 0, 1 ,0 ,0 ,1 ,1]),
np.array([0,1, 1, 0, 0 ,1 ,0 ,1 ,1]),
np.array([0,1, 1, 0, 1 ,1 ,0 ,1 ,1]),
np.array([0,1, 0, 1, 0 ,0 ,1 ,1 ,1]),
np.array([0,1, 1, 1, 1 ,1 ,1 ,1 ,1])]



where_1={}
for i in range(2,9):
    where_1[i]=[]
    for j in T[i]:
        where_1[i].append(set(np.where(1==j)[0]))


Order_of_T={}
Order_of_T[2]=[[{1},{2}],
[{1},{1,2}],[{1},{2}]]


Order_of_T[3]=[[{1},{2},{3}],
[{1},{1,2},{3}],
[{1},{1,2},{1,2,3}],
[{1},{1,2},{2,3}],
[{1},{2},{2,3}],
[{1},{2},{3}]]

Order_of_T[4]=[[{1},{2},{3},{4}],
[{1},{1,2},{3},{4}],
[{1},{1,2},{3},{3,4}],
[{1,3},{1,2},{3},{3,4}],
[{1,3},{1,2,3,4},{3},{3,4}],
[{1,3},{2,4},{3},{3,4}],
[{1,3},{2,4},{3},{4}],
[{1,3},{2},{3},{4}],
[{1},{2},{3},{4}]]


Order_of_T[5]=[[{1},{2},{3},{4},{5}],
[{1},{1,2},{3},{4},{5}],
[{1},{1,2},{3},{4},{4,5}],
[{1},{1,2},{3},{4},{1,2,4,5}],
[{1},{1,2},{3},{4},{1,2,3,4,5}],
[{1,3},{1,2},{3},{4},{1,2,3,4,5}],
[{1,3,4},{1,2},{3},{4},{1,2,3,4,5}],
[{1,4},{1,2},{3},{4},{1,2,3,4,5}],
[{1,4},{1,2},{3},{4},{2,3,5}],
[{1},{1,2},{3},{4},{2,3,5}],
[{1},{2},{3},{4},{2,3,5}],
[{1},{2},{3},{4},{3,5}],
[{1},{2},{3},{4},{5}]]


Order_of_T[6]=[[{1},{2},{3},{4},{5},{6}],
[{1},{1,2},{3},{4},{5},{6}],
[{1},{1,2,3},{3},{4},{5},{6}],
[{1},{2,3},{3},{4},{5},{6}],
[{1},{2,3},{3},{4},{4,5},{6}],
[{1},{2,3},{3},{4},{4,5,6},{6}],
[{1},{2,3},{3},{4},{5,6},{6}],
[{1},{2,3,5,6},{3},{4},{5,6},{6}],
[{1},{2,5,6},{3},{4},{5,6},{6}],
[{1},{2,5},{3},{4},{5,6},{6}],
[{1,2,5},{2,5},{3},{4},{5,6},{6}],
[{1,2,4,5},{2,5},{3},{4},{5,6},{6}],
[{1,4},{2,5},{3},{4},{5,6},{6}],
[{1,4,6},{2,5},{3},{4},{5,6},{6}],
[{1,3,4,6},{2,5},{3},{4},{5,6},{6}],
[{1,3,6},{2,5},{3},{4},{5,6},{6}],
[{1,3},{2,5},{3},{4},{5,6},{6}],
[{1},{2,5},{3},{4},{5,6},{6}],
[{1},{2,5},{3},{4},{5},{6}],
[{1},{2},{3},{4},{5},{6}],
[{1},{2},{3,4},{4},{5},{6}],
[{1},{2},{3},{4},{5},{6}]]

Order_of_T[7]=[[{1},{2},{3},{4},{5},{6},{7}],
[{1,3},{2},{3},{4},{5},{6},{7}],
[{1,3},{2},{3},{1,3,4},{5},{6},{7}],
[{1,3,5},{2},{3},{1,3,4},{5},{6},{7}],
[{1,3,5,7},{2},{3},{1,3,4},{5},{6},{7}],
[{1,3,7},{2},{3},{1,3,4},{5},{6},{7}],
[{1,3,7},{2},{3},{1,3,4,7},{5},{6},{7}],
[{1,3,7},{2},{3},{1,3,4,6,7},{5},{6},{7}],
[{1,3,7},{2},{3},{1,2,3,4,6,7},{5},{6},{7}],
[{1,3,7},{2},{3},{1,2,3,4,5,6,7},{5},{6},{7}],
[{1,3,7},{2},{3},{1,2,3,4,5,7},{5},{6},{7}],
[{1,3,7},{2},{3},{1,2,4,5,7},{5},{6},{7}],
[{1,3,7},{2},{3},{2,3,4,5},{5},{6},{7}],
[{1,3,7},{2},{3},{2,3,4},{5},{6},{7}],
[{1,3},{2},{3},{2,3,4},{5},{6},{7}],
[{1},{2},{3},{2,3,4},{5},{6},{7}],
[{1},{2},{3},{2,4},{5},{6},{7}],
[{1},{2},{3},{2,4,6},{5},{6},{7}],
[{1},{2},{3},{4,6},{5},{6},{7}],
[{1},{2},{3},{4},{5},{6},{7}],
[{1},{2},{3,5},{4},{5},{6},{7}],
[{1},{2,6},{3,5},{4},{5},{6},{7}],
[{1},{2,6},{2,3,5,6},{4},{5},{6},{7}],
[{1},{2,6},{3,5},{4},{5},{6},{7}],
[{1},{2},{3,5},{4},{5},{6},{7}],
[{1},{2},{3},{4},{5},{6},{7}],
[{1},{2},{3},{4},{5},{6,7},{7}],
[{1},{2},{3},{4},{5},{6},{7}],
[{1},{1,2},{3},{4},{5},{6},{7}],
[{1},{2},{3},{4},{5},{6},{7}]]

Order_of_T[8]=[[{1},{2},{3},{4},{5},{6},{7},{8}],
[{1,3},{2},{3},{4},{5},{6},{7},{8}],
[{1,3,8},{2},{3},{4},{5},{6},{7},{8}],
[{1,3,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,6,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,6,7},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,4,6,7},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,4},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,4,5},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,3,4,5,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,4,5,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,4,5,6,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,4,5,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,4,5,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,3,4,5,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,3,4,5,6,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,4,5,6,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,4,5,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,4,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,7,8},{2},{3},{4},{5},{6},{6,7},{8}],
[{1,2,7,8},{2},{3},{4},{5},{6},{6,7},{6,7,8}],
[{1,2,7,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,7,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,5,7,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,7,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,3,7,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,3,6,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,3,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{5},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{5,6,7},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{3,5,6,7},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{5,6,7},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{2,5,6,7},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{2,4,5,6,7},{6},{6,7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{2,4,5,6,7},{6},{7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{2,4,5,6},{6},{7},{7,8}],
[{1,2,3,5,8},{2},{3},{4},{2,4,5,6},{6},{7},{8}],
[{1,2,3,5,8},{2},{3},{4},{2,3,4,5,6},{6},{7},{8}],
[{1,2,3,5,8},{2},{3},{4},{2,3,5,6},{6},{7},{8}],
[{1,2,3,5,8},{2},{3},{4},{2,3,5,6,8},{6},{7},{8}],
[{1,2,3,5,8},{2},{3},{4},{2,3,5,8},{6},{7},{8}],
[{1},{2},{3},{4},{2,3,5,8},{6},{7},{8}],
[{1},{2},{3},{4},{3,5,8},{6},{7},{8}],
[{1},{2},{3},{4},{3,4,5,8},{6},{7},{8}],
[{1},{2},{3},{4},{3,4,5,7,8},{6},{7},{8}],
[{1},{2},{3},{4},{3,4,5,7},{6},{7},{8}],
[{1},{2},{3},{4},{3,4,5,7},{6},{4,7},{8}],
[{1},{2},{3},{4},{3,4,5,7},{6},{3,4,7},{8}],
[{1},{2},{3},{4},{3,4,5,7},{6},{2,3,4,7},{8}],
[{1},{2},{3},{4},{2,5},{6},{2,3,4,7},{8}],
[{1},{2},{3},{4},{5},{6},{2,3,4,7},{8}],
[{1},{2},{3},{4},{5},{6},{3,4,7},{8}],
[{1},{2},{3},{4},{5},{6},{4,7},{8}],
[{1},{2},{3},{4},{5},{6},{7},{8}]]


#CNOT gate form of T matrix
KLF_order={}
for i in range(2,9):
    KLF_order[i] = make_operation(where_1[i],Order_of_T[i])

#list of R matrix
r={}
r[2]=matrix([(1, 0, 0),
             (1, 1, 1),
             (0, 0, 1)])
r[3]=matrix([(1, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0),
 (0, 0, 1, 0, 1, 1),
 (0, 1, 0, 1, 1, 0),
 (0, 0, 0, 1, 0, 0)])
r[4]=matrix([(1, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 0, 0),
 (1, 1, 0, 1, 1, 0, 0, 0, 0),
 (1, 1, 1, 1, 1, 1, 1, 1, 1),
 (0, 1, 0, 1, 0, 1, 1, 0, 0),
 (0, 0, 0, 1, 0, 1, 0, 1, 0),
 (0, 0, 0, 0, 0, 1, 0, 0, 0)])
r[5]=matrix([(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1),
 (1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1),
 (1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1),
 (0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0),
 (0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)])
r[6]=matrix([(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1),
 (0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1),
 (1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0),
 (0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0),
 (0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1),
 (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)])
r[7]=matrix([(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1),
 (1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1),
 (1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0),
 (0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1),
 (0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0)])
r[8]=matrix([(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
 (0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1),
 (0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0),
 (0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1),
 (0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1),
 (1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1),
 (1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1),
 (1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1),
 (0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0),
 (0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1),
 (0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0),
 (0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0),
 (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)])


modulus_poly={16:t^16+t^5+t^3+t^1+1,32:t^32+t^7+t^3+t^2+1,
              64:t^64+t^4+t^3+t+1, 127: t^127+t^1+1 ,
              128:t^128+t^7+t^2+t^1+1, 163:t^163+t^7+t^6+t^3+1 ,
              233:t^233+t^74+1, 283:t^283+t^12+t^7+t^5+1,
              571:t^571+t^10+t^5+t^2+1,1024:t^1024+t^19+t^6+t+1}

CRT_para={16:[[2,2],[1,1],[2,1],[3,1],[1,1]],
          32:[[4,3],[1,2],[2,1],[3,1],[6,1]],
          64:[[6,6],[1,3],[2,1],[3,1],[6,1],[9,1]],            
          127:[[7,6],[1,3],[2,2],[3,1],[6,1],[9,1],[17,1]],
          128:[[5,5],[1,3],[2,2],[3,1],[6,1],[9,1],[18,1]],
          163:[[8,8],[1,4],[2,2],[3,2],[6,1],[9,1],[18,1],[6,1]],
          233:[[6,6],[1,4],[2,2],[3,2],[6,1],[9,1],[18,1],[24,1]],
          256:[[5,5],[1,4],[2,2],[3,2],[6,1],[9,1],[18,1],[30,1]],
          283:[[7,6],[1,4],[2,3],[3,2],[6,1],[9,1],[18,1],[30,1],[5,1]],
          571:[[9,8],[1,4],[2,3],[3,2],[6,2],[9,1],[18,1],[30,1],[56,1],[8,1]],
          1024:[[8,7],[1,4],[2,3],[3,2],[6,2],[9,1],[18,1],[30,1],[56,1],[99,1]]
          }

irr_list=[]
for i in range(1,11):
    irr_list.append(irr_poly(i))

    
ops1={}
ops={}
depth={}
tdepth={}

for i in [16,32,64,127,128,163,233,283,571,1024]:
    CRT=CRTMODMULT(CRT_para[i],i,modulus_poly[i]).decompose().decompose()
    count=CRT.count_ops()
    ops1[i] = (count['cx'],count['t'],count['tdg'],count['h'])
    ops[i] = (count['cx']+count['h'],count['t']+count['tdg'])    
    depth[i]=CRT.depth()
    tdepth[i]=CRT.depth(lambda gate: gate[0].name in ['t', 'tdg'])

print(ops)
print(depth)
print(tdepth)
