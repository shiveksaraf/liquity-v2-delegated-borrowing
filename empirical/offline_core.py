from collections import Counter
import copy
WAD=10**18
YEAR=365*86400
MIN_DEBT=2000*WAD
ZERO="0x"+"0"*40

class Replay:
    def __init__(self):
        self.troves={};self.batches={};self.Ldebt=0;self.Lcoll=0;self.shutdown=0
        self.rate_moves=[];self.operations=[];self.redemptions=[];self.counts=Counter()
        self.pending={};self.snapshots=[]
        self.previous_batches={};self.pending_rank={}
        self.capture_rank=False

    def batch_latest(self,b,t):
        period=max(0,min(t,self.shutdown or t)-b['last_debt'])
        interest=b['debt']*b['rate']*period//YEAR//WAD
        fee=b['debt']*b['fee']*period//YEAR//WAD
        return [b['shares'],b['debt']+interest+fee,b['coll'],interest,b['debt'],b['rate'],
                b['debt']*b['rate'],b['fee'],fee,b['debt']*b['fee'],b['last_debt'],b['last_rate']]

    def latest(self,p,t):
        rd=p['stake']*(self.Ldebt-p['snap_debt'])//WAD
        rc=p['stake']*(self.Lcoll-p['snap_coll'])//WAD
        if p['manager']==ZERO:
            rec=p['debt'];rate=p['rate'];period=max(0,min(t,self.shutdown or t)-p['last_debt'])
            interest=rec*rate*period//YEAR//WAD;fee=0;last=p['last_rate'];weight=rec*rate
        else:
            b=self.batch_latest(self.batches[p['manager']],t);share=p['shares'];total=b[0]
            rec=b[4]*share//total if total else 0
            interest=b[3]*share//total if total else 0
            fee=b[8]*share//total if total else 0
            rate=b[5];last=max(b[11],p['last_rate']);weight=rec*rate
        return [rec+rd+interest+fee,p['coll']+rc,rd,rc,interest,rec,rate,weight,fee,last]

    def apply(self,e):
        n,f,t=e['name'],e['fields'],e['timestamp'];self.counts[n]+=1
        if n=='ShutDown':self.shutdown=t
        elif n=='Liquidation':self.Ldebt=f['L_boldDebt'];self.Lcoll=f['L_ETH']
        elif n in ('TroveUpdated','BatchedTroveUpdated'):
            key=f['troveId'];old=self.troves.get(key)
            self.pending[key]=copy.deepcopy(old)
            if self.capture_rank and old and old['status'] in (1,4):
                target=self.latest(old,t)[6]
                ds=[(self.latest(p,t)[6],self.latest(p,t)[0]) for p in self.troves.values() if p['status'] in (1,4)]
                total=sum(d for r,d in ds)
                self.pending_rank[key]={'total_debt':total,'debt_below':sum(d for r,d in ds if r<target),
                                        'debt_at_or_below':sum(d for r,d in ds if r<=target)}
            p=copy.deepcopy(old) if old else {'status':1,'last_rate':t,'last_debt':0,'debt':0,'rate':0,'shares':0,'manager':ZERO}
            p.update(coll=f['coll'],stake=f['stake'],snap_coll=f['snapshotOfTotalCollRedist'],snap_debt=f['snapshotOfTotalDebtRedist'])
            if n=='TroveUpdated':p.update(debt=f['debt'],rate=f['annualInterestRate'],last_debt=t,manager=ZERO,shares=0)
            else:p.update(manager=f['interestBatchManager'],shares=f['batchDebtShares'],debt=0,rate=0,last_debt=0)
            self.troves[key]=p
        elif n=='BatchUpdated':
            key=f['interestBatchManager'];old=self.batches.get(key)
            self.previous_batches[key]=copy.deepcopy(old)
            b=dict(debt=f['debt'],coll=f['coll'],rate=f['annualInterestRate'],fee=f['annualManagementFee'],shares=f['totalDebtShares'],
                   last_debt=0 if f['operation']==0 else t,last_rate=t if f['operation'] in (0,2) else old['last_rate'])
            self.batches[key]=b
            if f['operation']==2:
                self.rate_moves.append(dict(e,controller=key,kind='batch',old_rate=old['rate'],new_rate=b['rate'],
                                            upfront_fee_wei=f['debtIncreaseFromUpfrontFee'],debt_wei=b['debt'],
                                            elapsed=t-old['last_rate']))
        elif n=='TroveOperation':
            key=f['troveId'];p=self.troves[key];op=f['operation'];old=self.pending.get(key)
            if op==4 and old and old['manager']!=ZERO:
                # onApplyTroveInterest emits TroveUpdated even when the trove remains
                # batched. The preceding BatchUpdated exposes the exact share delta.
                manager=old['manager'];before=self.previous_batches[manager];after=self.batches[manager]
                p.update(manager=manager,shares=old['shares']+after['shares']-before['shares'],debt=0,rate=0,last_debt=0)
            if op in (0,3,7,8,9):p['last_rate']=t
            if op==1:p['status']=2
            elif op==5:p['status']=3
            elif op in (0,7):p['status']=1
            elif op==6:
                # Status threshold uses exact pre-operation debt minus redeemed amount.
                debt_before=self.latest(old,t)[0] if old else None
                newdebt=debt_before+f['debtChangeFromOperation'] if debt_before is not None else None
                if not self.shutdown and newdebt is not None and newdebt<MIN_DEBT:p['status']=4
                self.redemptions.append(dict(e,trove=key,redeemed_wei=-f['debtChangeFromOperation'],
                                             rate_before=self.latest(old,t)[6] if old else None,
                                             rate_rank=self.pending_rank.get(key),
                                             rank_status='Debt-weighted rate-rank interval among outstanding active/zombie troves; exact tie-queue/oracle eligibility NOT IDENTIFIED'))
            elif op in (2,4) and p['status']==4:
                # Activation can occur in BorrowerOperations before its TroveManager event.
                newdebt=self.latest(old,t)[0]+f['debtChangeFromOperation']+f['debtIncreaseFromUpfrontFee'] if old else 0
                if newdebt>=MIN_DEBT:p['status']=1
            row=dict(e,trove=key,operation=op,upfront_fee_wei=f['debtIncreaseFromUpfrontFee'])
            self.operations.append(row)
            if op==3:
                self.rate_moves.append(dict(e,controller=str(key),kind='individual',old_rate=old['rate'],new_rate=p['rate'],
                                            upfront_fee_wei=f['debtIncreaseFromUpfrontFee'],debt_wei=p['debt'],elapsed=t-old['last_rate']))