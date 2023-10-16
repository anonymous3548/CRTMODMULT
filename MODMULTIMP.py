from qiskit import QuantumRegister, ClassicalRegister, QuantumCircuit, assemble, Aer
from qiskit.circuit.library import Permutation
from qiskit.quantum_info import Statevector
from qiskit.quantum_info import Operator
from qiskit.visualization import plot_histogram
import numpy as np
import copy

def mat_gen(k,f):
    Rf=S.quotient(f)
    return matrix([Rf((1+t^k)*t^j).list() for j in range(f.degree())]).transpose()

def mult1xk(k,n):
    l=max(0,2*n-1-k)    
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(k+2*n-1)
    qc = QuantumCircuit(A,B,C)
        
    if n>1:
        for i in range(k,k+l):
            qc.cx(C[int(i+k)],C[int(i)])
        for i in range(k):
            qc.cx(C[int(i+k)],C[int(i)])
            
        sub_inst = kmult(n).to_instruction()
        qc.append(sub_inst,[A[j] for j in range(n)]+[B[j] for j in range(n)]+[C[j] for j in range(k,2*k+l)])
            
        for i in range(k):
            qc.cx(C[int(i+k)],C[int(i)])
        for i in range(k,k+l):
            qc.cx(C[int(i+k)],C[int(i)])
        return qc.decompose()
            
    else:
        qc.cx(C[int(k)],C[int(0)])
        qc.ccx(A[int(0)],B[int(0)],C[int(k)])    
        qc.cx(C[int(k)],C[int(0)])
        return qc
    
    
def kmult(n):
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(2*n-1)
    qc = QuantumCircuit(A,B,C)
    
    k=int((n+1)/2)
    
    if n>1:
        sub_inst = mult1xk(k,k).to_instruction()
        qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(3*k-1)])       
        
        sub_inst = mult1xk(k,n-k).to_instruction()
        
        qc.append(sub_inst,[A[j] for j in range(k,n)]+[B[j] for j in range(k,n)]+[C[j] for j in range(k,2*n-1)])
        
        
        for i in range(n-k):
            qc.cx(A[int(i+k)],A[int(i)])
        for i in range(n-k):
            qc.cx(B[int(i+k)],B[int(i)])
            
        sub_inst = kmult(k).to_instruction()
        qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(k,3*k-1)])
        
        for i in range(n-k):
            qc.cx(B[int(i+k)],B[int(i)])
        for i in range(n-k):
            qc.cx(A[int(i+k)],A[int(i)]) 
        return qc.decompose()
            
    else:
        qc.ccx(A[int(0)],B[int(0)],C[int(0)])
        return qc
    
def modmultimp(n,modulus):
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(n)
    qc = QuantumCircuit(A,B,C)
    
    k=int((n+1)/2)
    
    sub_inst = kmult(k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(2*k-1)])  
    
    
    
    sub_inst = modshift(modulus,k).inverse().to_instruction()
    qc.append(sub_inst,[C[j] for j in range(n)])
        
    sub_inst = kmult(n-k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k,n)]+[B[j] for j in range(k,n)]+[C[j] for j in range(2*(n-k)-1)])      
    
    
    P,L,U=mat_gen(k,modulus).LU()
    sub_inst = in_place(P,L,U).to_instruction()
    qc.append(sub_inst,[C[j] for j in range(n)])       
    
    
    for i in range(n-k):
        qc.cx(A[int(i+k)],A[int(i)])
    for i in range(n-k):
        qc.cx(B[int(i+k)],B[int(i)])    
    
    sub_inst = kmult(k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(2*k-1)])  

    for i in range(n-k):
        qc.cx(B[int(i+k)],B[int(i)])
    
    for i in range(n-k):
        qc.cx(A[int(i+k)],A[int(i)])
    
    sub_inst = modshift(modulus,k).to_instruction()
    qc.append(sub_inst,[C[j] for j in range(n)])

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


def modshift(f,l):
    b = f.degree()
    C = QuantumRegister(b)
    qc = QuantumCircuit(C)
    
    Perm=Permutation(b,[(k-l)%b for k in range(b)])
    sub_inst = Perm.to_instruction()
    qc.append(sub_inst,[C[j] for j in range(b)])
    
    tmp=np.array(f.list())
    tmp1=np.where(tmp==1)[0]
    
    for j in range(l):
        for i in range(1,len(tmp1)-1):
            qc.cx(C[int((0+j)%b)],C[int((tmp1[i]+j)%b)])
    return qc



def modmult(n,modulus):
    A = QuantumRegister(n)
    B = QuantumRegister(n)
    C = QuantumRegister(n)
    qc = QuantumCircuit(A,B,C)
    k=int((n+1)/2)

    for i in range(n-k):
        qc.cx(A[int(i+k)],A[int(i)])
    for i in range(n-k):
        qc.cx(B[int(i+k)],B[int(i)])    
    
    sub_inst = kmult(k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(2*k-1)])  

    for i in range(n-k):
        qc.cx(B[int(i+k)],B[int(i)])
    
    for i in range(n-k):
        qc.cx(A[int(i+k)],A[int(i)])    
    
    P,L,U=mat_gen(k,modulus).LU()
    sub_inst = in_place(P,L,U).inverse().to_instruction()
    qc.append(sub_inst,[C[j] for j in range(n)])        
    
    sub_inst = kmult(n-k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k,n)]+[B[j] for j in range(k,n)]+[C[j] for j in range(2*(n-k)-1)])        
    
    for i in range(k):
        sub_inst = modshift(modulus).to_instruction()
        qc.append(sub_inst,[C[j] for j in range(n)])    
    
    sub_inst = kmult(k).to_instruction()
    qc.append(sub_inst,[A[j] for j in range(k)]+[B[j] for j in range(k)]+[C[j] for j in range(2*k-1)])  
    
    P,L,U=mat_gen(k,modulus).LU()
    sub_inst = in_place(P,L,U).to_instruction()
    qc.append(sub_inst,[C[j] for j in range(n)])           
  
    return qc


k = GF(2)
S.<t> = PolynomialRing(k)


modulus_poly={16:t^16+t^5+t^3+t^1+1, 32:t^32+t^7+t^3+t^2+1,64:t^64+t^4+t^3+t+1, 127: t^127+t^1+1 ,128:t^128+t^7+t^2+t^1+1, 163:t^163+t^7+t^6+t^3+1 ,233:t^233+t^74+1, 283:t^283+t^12+t^7+t^5+1,571:t^571+t^10+t^5+t^2+1,1024:t^1024+t^19+t^6+t+1}




ops={}
ops1={}
depth={}
tdepth={}


for i in [16,32,64,127,128,163,233,283,571,1024]:
    imp=modmultimp(i,modulus_poly[i]).decompose().decompose()
    count=imp.count_ops()
    ops1[i] = (count['cx'],count['t'],count['tdg'],count['h'])
    ops[i] = (count['cx']+count['h'],count['t']+count['tdg'])    
    depth[i]=imp.depth()
    tdepth[i]=imp.depth(lambda gate: gate[0].name in ['t', 'tdg'])

print(ops)
print(depth)
print(tdepth)
