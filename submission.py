# implemeneted cancel of orders
# clean up

import time
st_time=time.time()

from heapq import heappush, heappop, heapify
from collections import deque,defaultdict,Counter
import itertools
from itertools import permutations,combinations
import sys
import bisect
import string
import math
import random
def I():
    return int(input())
def MI():
    return map(int,input().split())
def LI():
    return [int(i) for i in input().split()]
def LI_():
    return [int(i)-1 for i in input().split()]
def show(*inp,end='\n'):
    if show_flg:
        print(*inp,end=end)
YN=['Yes','No']
mo=10**9+7
inf=float('inf')
ts=time.time()
#sys.setrecursionlimit(10**6)
#input=sys.stdin.readline

show_flg=False
#show_flg=True

drop_probability=1

def dijkstra(edge,st):
    # initialize: def: d=dist(st,i), prev=[previous vertex in minimum path], q[]
    n=len(edge)
    d=[(0 if st==i else inf,i) for i in range(n)]
    prev=[0]*n
    q=[i for i in d]
    heapify(q)
    
    # calc
    while q:
        dist,cur=heappop(q)
        for dst,dist in edge[cur]:
            alt=d[cur][0]+dist
            if alt<d[dst][0]:
                d[dst]=(alt,dst)
                prev[dst]=cur
                heappush(q,(alt,dst))
    dist=[i for i,j in d]
    return dist,prev

def dijkstra_w_light(edge,st,t):
    # initialize: def: d=dist(st,i), prev=[previous vertex in minimum path], q[]
    global P
    show('dij called',st,t,P)
    n=len(edge)
    d=[(0 if st==i else inf,i) for i in range(n)]
    prev=[0]*n
    q=[i for i in d]
    heapify(q)
 
    # calc
    while q:
        dist,cur=heappop(q)
        for dst,dist,ei in edge[cur]:
            if ei==5:
                time_at_light=t+d[cur][0]+dist
                if time_at_light%(2*P)<P:
                    wt=0
                else:
                    wt=2*P-time_at_light%(2*P)
                alt=d[cur][0]+dist+wt
            else:
                alt=d[cur][0]+dist
            if alt<d[dst][0]:
                d[dst]=(alt,dst)
                prev[dst]=cur
                heappush(q,(alt,dst))
    dist=[i for i,j in d]
    return dist,prev
 
V,E=MI()
roads=[]
for i in range(E):
    roads.append(MI())

f=LI()
t=[LI() for i in range(4)]
P=I()
tw=I()
T=I()
order=[0]*(T+10)
order_detail=[(0,0) for i in range(T+10)]
accor=[0]*(T+10)
order_time=[]

g=[[[] for _ in range(V+1)] for d in range(16)]
c=[]
neighber=[set() for _ in range(V+1)]
d_map=[{} for _ in range(V+1)]
mins=[[[] for _ in range(V+1)] for d in range(16)]
prevs=[[[] for _ in range(V+1)] for d in range(16)]
exp_wt=1+P//4

for u,v,d,e1,e2 in roads:
    for dd in range(16):
        g[dd][u].append((v,(10 if 1<=e1<=4 and (1<<(e1-1))&dd>0 else 1)*d+(exp_wt if e1==5 else 0)))
        g[dd][v].append((u,(10 if 1<=e2<=4 and (1<<(e2-1))&dd>0 else 1)*d+(exp_wt if e2==5 else 0)))
    c.append((u,v,d,e1,e2))
    neighber[u].add(v)
    neighber[v].add(u)
    d_map[u][v]=d
    d_map[v][u]=d

for dd in range(16):
    for i in range(1,V+1):
        min_dist,prev=dijkstra(g[dd],i)
        mins[dd][i]=min_dist
        prevs[dd][i]=prev

#show('order',order)
order_at_shop=[] # stock (vertex, order_time)
item_at_car=[[] for _ in range(V+1)] # stock order time at each vertex
num_item_at_car=0
moves=[]

def min_update(t,jam_d=0):
    for i in range(1,V+1):
        min_dist,prev=dijkstra_w_light(g[jam_d],i,t)
        mins[jam_d][i]=min_dist
        prevs[jam_d][i]=prev

def move(v):
    global moves
    print(v)
    sys.stdout.flush()
    moves.append(v)
    return v

def ship():
    show(order_at_shop)
    global num_item_at_car
    while order_at_shop:
        v,t=order_at_shop.pop()
        item_at_car[v].append(t)
        num_item_at_car+=1
    show('item_at_car',item_at_car)

def cancel_order(v_can,t_can):
    global num_item_at_car
    if (v_can,t_can) in order_at_shop:
        order_at_shop.remove((v_can,t_can))
        show('canceled at shop',v_can,t_can)
    if t_can in item_at_car[v_can]:
        item_at_car[v_can].remove(t_can)
        num_item_at_car-=1
        show('canceled at car',v_can,t_can)

def deliver(v,deliver_t):
    global num_item_at_car
    d_p=0
    while item_at_car[v]:
        or_t=item_at_car[v].pop()
        num_item_at_car-=1
        d_p+=T**2-(deliver_t-or_t)**2
##    show("delivered to",v,"deliverPoint",d_p)
    return d_p

def stat_init():
    global order_at_shop
    global item_at_car
    global num_item_at_car
    order_at_shop=[] # stock (vertex, order_time)
    item_at_car=[[] for _ in range(V+1)] # stock order time at each vertex
    num_item_at_car=0

def root_valuator(current,now,root,f_info=True):
    if len(root)==0:
        return 0,0
    global item_at_car
    cur=current
    point=0
    rt=now
    for next_dest,dist in root[::-1]:
        if len(item_at_car[next_dest])>0:
            rt+=dist
            for j in item_at_car[next_dest]:
                point+=T**2-(rt-j)**2
        cur=next_dest
    return point,rt-now

def neighber_search(cur,next_dest,effc,best_p,best_d,f_info=True,jam_d=0):
    global item_at_car
    drop=[]
    n_item=0
    for nb,dist in g[jam_d][cur]:
        if nb==next_dest:continue
        if len(item_at_car[nb])>n_item:
            n_item=len(item_at_car[nb])
            drop_effc=(best_p+n_item*(T**2))/(mins[jam_d][cur][nb]*2+best_d)
            #if random.random()<drop_effc/effc:
            if drop_effc>=effc:
                drop=[(cur,mins[jam_d][nb][cur]),(nb,mins[jam_d][cur][nb])]
    return drop

def optimizer_drop(current,now,root,effc,best_p,best_d,f_info=True,jam_d=0):
    ##    show('!Optimizing',root)
    global item_at_car
    opt_root=[]
    cur=current
    org_now=now
    org_effc=effc
    n=len(root)
    
    for i in range(1,n+1):
        next_dest,dist=root[-i]
        drop=[]
        alt=0
        n_item=0
        for nb,d_nb in g[jam_d][cur]:
            if nb==next_dest:continue
            if len(item_at_car[nb])>n_item:
                #n_item=len(item_at_car[nb])
                rt=now+d_nb
                for j in item_at_car[nb]:
                    alt+=T**2-(rt-j)**2
                if prevs[0][nb][next_dest]==nb: # nb connected to next_dest ( possible enhancement mins[prevs[nb][next_dest]][next_dest]==mins[nb][next_dest] )
                    drop_time=mins[jam_d][cur][nb]+mins[jam_d][nb][next_dest]-dist
                    drop_effc=(best_p+alt)/(drop_time+best_d)
                    if drop_effc>=effc:
                        effc=drop_effc
                        drop.append((nb,mins[jam_d][cur][nb]))
                        drop.append((next_dest,mins[jam_d][nb][next_dest]))
                elif 0==1:
                    drop_time=mins[jam_d][cur][nb]*2
                    drop_effc=(best_p+alt)/(drop_time+best_d)
                    if drop_effc>=effc:
                        effc=drop_effc
                        drop.append((nb,mins[jam_d][cur][nb]))
                        drop.append((cur,mins[jam_d][nb][cur]))
                        drop.append((next_dest,mins[jam_d][cur][next_dest]))
        
        if drop:
            opt_root+=drop
            now+=drop_time
    ##            show('#yorimichi',drop)
        else:
            opt_root.append((next_dest,dist))
            now+=dist
        cur=next_dest
    
    # opt_root validation
    opt_valid=True
    cur=current
    for next_dest,dist in opt_root:
        if next_dest in neighber[cur]:
            if d_map[cur][next_dest]!=dist:
                opt_valid=False
            else:
                0 # validation ok
        else:
            opt_valid=False
        
        cur=next_dest
    
    if opt_valid:
        p,t=root_valuator(current,org_now,opt_root,f_info=False)
        opt_effc=p/t if t!=0 else 0
        if org_effc<=opt_effc:
            rt=opt_root[::-1]
        else:
            rt=root
    else:
    ##        show('!!optimization failed')
        rt=root
    
    return jam_root_converter(cur,rt)

def jam_root_converter(cur,root):
    if root:
        root.append((cur,0))
        no_jam_root=[]
        for i in range(len(root)-1):
            p,x=root[i]
            nx,x=root[i+1]
            no_jam_root.append((p,d_map[p][nx]))
    else:
        no_jam_root=[]
    return no_jam_root

def root_generator(cur,deliver_point,jam_d=0):# generate root
    root=[]
    p=deliver_point
    while p!=cur:
        prev_p=prevs[jam_d][cur][p]
        root.append((p,mins[jam_d][p][prev_p]))
        p=prev_p
    return jam_root_converter(cur,root)

def best_deliver(cur,now,item_at_car,f_info=True,optimize_mode=True,sim_mode=False,jam_d=0):
    global order_at_shop
    global num_item_at_car
    if sim_mode:
        item_at_car=[[i for i in order] for orders in sim_item_at_car]
    
    effc=0
    best_p,best_d=0,inf
    deliver_point=1
    # direct go
    for dest in range(2,V+1):
        if dest==cur:continue
        d=mins[jam_d][cur][dest]
        rt=now+d
        alt=0
        for j in item_at_car[dest]:
            alt+=T**2-(rt-j)**2
        if alt/d>effc:
            effc,best_p,best_d=alt/d,alt,d
            deliver_point=dest
    # turn to shop and go
    if cur!=1:
        db=mins[jam_d][cur][1]
        nx_item_at_car=[[] for i in range(1+V)]
        for order_v,t in order_at_shop:
            nx_item_at_car[order_v].append(t)
        for i in range(2,1+V):
            for t in item_at_car[i]:
                nx_item_at_car[i].append(t)
        if f_info:
            for t in range(min(now+1,T-1),min(now+db+1,T)):
                v=order[t][1]
                if v!=0:
                    nx_item_at_car[v].append(t)
        for dest in range(2,V+1):
            if cur==1:break
            if dest==cur:continue
            dg=mins[jam_d][1][dest]
            rt=now+db+dg
            d=db+dg
            alt=0
            for j in nx_item_at_car[dest]:
                alt+=T**2-(rt-j)**2
            if alt/d>effc:
                effc,best_p,best_d=alt/d,alt,d
                deliver_point=1

    # optimize
    if deliver_point==1:
        0
    else:
        if optimize_mode:
            root=optimizer_drop(cur,now,root,effc,best_p,best_d,f_info=False,jam_d=jam_d)
    # opt end

    # generate root
    root=root_generator(cur,deliver_point,jam_d=jam_d)
 
    return deliver_point,root,effc

def rand_move(cur,now,jam_d=0):
    n=len(g[0][cur])
    x=random.randint(0,n-1)
    dest,dist=g[0][cur][x]
    root=[(dest,dist)]
    return 0,root,0

# recieve info
def interactive(wait_num):
    global item_at_car
    stop_flag=False
    stat_init()
    state=0 # 0 on vertex, 1 on road
    final_dest=1
    dest=1
    cur=1
    point=0
    effc=0
    cur_jam=0
    wait_status=False
    current_action=-1
    root=[]
    dist=inf
    
    for t in range(T):
        car_status=input()
        jam_info=LI()
        cur_jam=sum([jam_info[i]<<i for i in range(4)])
        Ncan=I()
        for j in range(Ncan):
            can_id=I()
            v_can,t_can=order_detail[can_id]
            cancel_order(v_can,t_can)
            
        Nnew=I()
        v=0
        for j in range(Nnew):
            new_id,v=MI()
            order_at_shop.append((v,t))# stock (vertex, order_time)
            order[t]=(new_id,v)
            order_detail[new_id]=(v,t)

        Nput=I()
        for j in range(Nput):
            put_id=I()

        show('items',item_at_car,order_detail[:10])
        ##show('state',state,'cur',cur,'dest',dest,'dist',dist,'final_dest',final_dest,'root',root)

        if car_status=='BROKEN':
            current_action=move(-1)
            show('Stay due to broken at',cur)
        elif wait_status:
            current_action=move(-1)
            show('waiting at ',cur)
        else:
            if state==0: # at vertex
                if cur==1:
                    ship()
                else:
                    point+=deliver(cur,t)
                    
                if final_dest==cur:
                    deliver_point,root,effc=best_deliver(cur,t,item_at_car,optimize_mode=False,f_info=False,jam_d=cur_jam)
                    #deliver_point,root,effc=rand_move(cur,t,jam_d=cur_jam)
                    ##show('bd',root,item_at_car,order_at_shop)
                    if root:
                        final_dest=root[0][0]
                    else:
                        deliver_point,root,effc=rand_move(cur,t,jam_d=cur_jam)
                        final_dest=root[0][0]
                        ##show('random',root)

                dest,dist=root.pop() # not to do in waiting or jam
                state=1
                current_action=move(dest)

            else:
                current_action=move(dest)

        vardict = input()
        
        if vardict == 'NG':
            #import everything_
            exit()
        elif vardict=='JAM':
            show('Jam in going to',current_action)
            current_action=-1
            wait_status=False
        elif vardict[0]=='W': # WAIT
            wait_time=int(vardict[5:])
            wait_status=True
        else:
            wait_status=False
        
        #移動判定
        if current_action!=-1:
            dist-=1
            state=1
            if dist==0:
                cur=dest
                state=0
        
        Nachive = int(input())
        for j in range(Nachive):
            achive_id=I()

    return point

point=interactive(wait_num=0)
