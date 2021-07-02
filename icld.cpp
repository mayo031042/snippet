// きれいなコード
#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <queue>
#include <map>
#include <set>
#include <cmath>

using namespace std;
using ll = long long int;
using vi = vector<int>;
using vll = vector<ll>;
using ss = string;
using db = double;
template<class T> using minpq = priority_queue <T,vector<T>,greater<T>>;
const int dx[4] = {1,0,-1,0};
const int dy[4] = {0,1,0,-1};
#define V vector
#define pii pair<int,int>
#define pll pair<ll,ll>
#define rep(i,s,n) for(int i=(s);i<(int)(n);i++)
#define all(v) v.begin(),v.end()
#define rall(v) v.rbegin(),v.rend()
#define sz(x) int(x.size())
template<class T>void chmax(T &x,T y){x=max(x,y);}
template<class T>void chmin(T &x,T y){x=min(x,y);}


// UF
typedef class uf_ uf_;
class uf_{
    using T = int;
private:
    T n,alln;
    V<T> par;

public:
    uf_(int sz){
        n=alln=sz;
        par.resize(n,-1);
    }

    int rt(int x){
        if(par[x]<0)return x;
        return par[x]=rt(par[x]);
    }
    int size(int x){
        return -par[rt(x)];
    }
    int allsz(){
        return alln;
    }
    bool issame(int x,int y){
        return rt(x)==rt(y);
    }
    void unt(int x,int y){
        x=rt(x);y=rt(y);
        if(issame(x,y)) return ;
        if(size(x)<size(y))swap(x,y);
        par[x]+=par[y];
        par[y]=x;
        alln--;
        return ;
    }
};


//日付計算
bool uru(int year){
    if(year%400==0) return true;
    if(year%100==0) return false;
    if(year%  4==0) return true;
    return false;
}
void nxday(int &year,int &month,int &day){
    day++;
    if(month==2){
        if(day==30 or ( day==29 and !uru(year) )) day=1,month++;
    }
    else if(day==32){
        day=1,month++;
        if(month==13) month=1,year++;
    }
    else if(day==31){
        if(month==4 || month==6 || month==9 || month==11) day=1,month++;
    }
}
void preday(int &year,int &month,int &day){
    day--;
    if(day!=0)return ;
    day=31,month--;
    if(month==2){
        day=28;
        if(uru(year)) day=29;
    }
    else if(month==0) month=12,year--;
    else if(month==4 || month==6 || month==9 || month==11) day=30;
}


// seg木
typedef class seg_ seg_;
class seg_{
    using T = ll;
    int n;
    T base;
    V<T> dat;
    void build(const V<T> &v){
        rep(i,0,sz(v)) dat[i+n-1]=v[i];
        for(int now=n-2; now>=0; now--){
            dat[now]=func(dat[now*2+1],dat[now*2+2]);
        }
    }

    void influence(int i){
        int now=i+n-1;
        while(now){
            int par=(now-1)/2;
            int chi=par*2+1;
            if(now==chi)chi++;

            dat[par]=func(dat[now],dat[chi]);
            now=par;
        }
    }

    T range(int a,int b){
        return range_(a,b,0,0,n);
    }

public:
    seg_(const V<T> &v,T BASE):base(BASE){
        n=1;
        while(n<sz(v))n<<=1;

        dat.resize(n*2-1,base);
        build(v);
    }
    void set(int i,T x){
        dat[i+n-1]=x;
        influence(i);
    }
    void add(int i,T x){
        dat[i+n-1]=func(dat[i+n-1],x);
        influence(i);
    }

    T range_(int a,int b,int now,int l,int r){
        if(a<=l && r<=b)return dat[now];
        if(r<=a || b<=l)return base;
        return func(range_(a,b,now*2+1,l,(l+r)/2), range_(a,b,now*2+2,(l+r)/2,r));
    }
    
    inline T operator[](int i){ return dat[i+n-1]; }
    void print(){ int x,y=x=2; rep(now,0,n*2-1){ cout<<dat[now]<<","; if(y==x++){y<<=1;cout<<endl; }}}
    T    func(T l,T r){ return
/*関数*/        max(l,r)     ; }
};


// 遅延seg木
typedef class lazy_ lazy_;
class lazy_{
    using T = ll;
    T base,impos;
    int n;
    V<T> dat,lazy;

    void build(const V<T>&v){
        rep(i,0,sz(v))dat[i+n-1]=v[i]; 
        for(int now=n-2; now>=0; now--){ 
            dat[now]=func(dat[now*2+1],dat[now*2+2]); 
        }
    }

    void eval(int now){ 
        if(lazy[now]==impos)return ;
        if(now<n-1) lazy[now*2+1]=lazy[now*2+2]=lazy[now]; 
        dat[now]=lazy[now]; lazy[now]=impos; 
    }

    void update(int a,int b,T x,int now,int l,int r){ 
        eval(now); 
        if(a<=l && r<=b){ 
            lazy[now]=x;
            eval(now); 
        }
        else if(a<r && l<b){
            update(a,b,x,now*2+1,l,(l+r)/2);
            update(a,b,x,now*2+2,(l+r)/2,r);
            dat[now]=func(dat[now*2+1],dat[now*2+2]); 
        }
    }

    T range_(int a,int b,int now,int l,int r){ 
        eval(now); 
        if(a<=l && r<=b)return dat[now]; 
        if(r<=a || b<=l)return base; 
        return func( range_(a,b,now*2+1,l,(l+r)/2), range_(a,b,now*2+2,(l+r)/2,r)); 
    }

public:
    lazy_(const V<T>&v, T BASE, T IMPOS): base(BASE),impos(IMPOS){
        n=1;
        while(n<sz(v))n<<=1; 
        dat.resize(n*2-1,base);
        lazy.resize(n*2-1,impos);
        build(v); 
    }
    
    void confirm(int i){
        return update(i,i+1,impos,0,0,n); 
    }
    void set(int i,T x){ 
        confirm(i); 
        dat[i+n-1]=x;
        confirm(i); 
    }
    void add(int i,T x){
        confirm(i);
        dat[i+n-1]=func(dat[i+n-1],x);
        confirm(i);
    }

    void update(int a,int b,T x){ 
        return update(a,b,x,0,0,n); 
    }
    T    range(int a,int b){
        return range_(a,b,0,0,n); 
    }

    inline T operator[](int i){ 
        if(0<=i && i<n)return range(i,i+1); 
        return impos;
    }
    void print(){
        int x,y=x=2; 
        rep(now,0,n*2-1){ 
            cout<<dat[now]<<",";
            if(y==x++){y<<=1;cout<<endl; }
        }
    }
    T    func(T l,T r){ return 
/*関数!*/ max(l,r)           ; }
};


// fenwick tree -> segment treeの軽量版　転倒数の計算にも使える
typedef class fen_ fen_;
class fen_{
private:
    using T = int ;
    T n;
    V<T> bit;

public:
    fen_(T sz) : bit(sz+1,0){n = sz; }

    // a_i += val;
    void add(T i,T val){
        for( T x = i; x <= n; x += x&-x ){
            bit[x]+=val;
        }
    }

    // [1,i] の合計を計算
    T sum(T i){
        T ret=0;
        for(T x = i; x > 0; x -= x&-x ){
            ret+=bit[x];
        }
        return ret;
    }

    // [left+1,right] の合計を計算
    T sum(T left,T right){
        return sum(right) - sum(left);
    }

    // 転倒数を計算 v は1_indexed な配列、[1,n]の順列並び替えが望ましい
    ll inv(const V<T>&v){
        ll ret=0;
        rep(i,0,n){
            ret+=i-this->sum(v[i]);
            this->add(v[i],1);
        }
        return ret;
    }
};


// class ed
typedef class ed ed;
class ed{
    ed(int x,int y){
        ad=x;
        ds=y;
    }
    int ad;
    int ds;
};


// Sieve of Eratosthenes
vi prm, era_vec;
void era_init(int prm_sz){
    era_vec.resize(prm_sz,1);
    rep(i,2,prm_sz){
        if(era_vec[i]==1){
            prm.push_back(i);
            for(int j=i;j<prm_sz;j+=i) era_vec[j]=0;
        }
    }
}


// nCk -> P (mod) の値を指定しているか注意！
ll P;
vll fac, vac, inv;
void comb_init(int comb_sz){
    fac.resize(comb_sz,1);
    vac.resize(comb_sz,1);
    inv.resize(comb_sz,1);
    rep(i,2,comb_sz){
        fac[i]=i*fac[i-1] %P;
        inv[i]=P -(P/i)*inv[P%i] %P;
        vac[i]=inv[i]*vac[i-1] %P; 
    }
}
ll nck(int n,int k){
    if(n<k or k<0)return 0;
    return fac[n]*vac[n-k] %P*vac[k] %P;
}


// 三角関数　引数にはradian 値を使用する
const db rad_pi=3.141592653589793;
db rad_to_rad(db angle){
    return angle*rad_pi/180.0; 
}
db rad_to_deg(db radian){
    return radian*180/rad_pi;
}
db rad_art(db x,db y,db x_,db y_){ // A,B が原点中心に何radian差があるか判定
    db th=atan2(y_,x_) - atan2(y,x);
    if(th<-rad_pi)th+=2*rad_pi;
    else if(rad_pi<th)th-=2*rad_pi;
    return th;
}
void rad_rotate(db &x, db &y, db radian, db cx=0, db cy=0){
    db sinS=sin(radian);
    db cosS=cos(radian);
    db x_=x-cx;
    db y_=y-cy;
    x = x_*cosS - y_*sinS + cx;
    y = x_*sinS + y_*cosS + cy;
}


// 進数表記変換
char ntt_char(int x){
    if(x<10)return x+'0';
    return x-10+'a';
}
int ntt_int(char c){
    if('0'<=c and c<='9') return c-'0';
    return c-'a'+10;
}
ss ntt_cng(ss x,ll from,ll to){
    ll y=0,z=1;
    for(int i = sz(x)-1; i >= 0; i--){
        y+=z*ntt_int(x[i]);
        z*=from;
    }
    ss res="";
    while(y){
        res=ntt_char(y%to)+res;
        y/=to;
    }
    return res;
}
ss ntt_erase0(ss s){
    int pos=-1;
    rep(i,0,sz(s)){
        if(s[i]!='0'){
            pos=i;
            break;
        }
    }
    if(pos==-1)return "0";
    return s.substr(pos,sz(s));
}




typedef class cyc_ cyc_;
class cyc_{
    using T = ll;
private:
    V<T> v;ll tail=-1,cycle=0;
public:
    cyc_(){}
    T func(T x){
    
        return x;
    }
    void survey(T x){map<T,int>mp;while(!mp.count(x)){mp[x]=cycle++;v.push_back(x);x=func(x);}tail=mp[x];cycle-=tail;}
    T res(T x,ll n){if(tail==-1)survey(x);ll tm=min(n,tail);tm+=(n-tm)%cycle;return v[tm];}
};


// 周期性を持って変化するｘについて、ｎ回目の変化を算出する（計算量は無視しているので遅いかも、、、）
typedef class cyc_ cyc_;
class cyc_{
    using T = ll;
private:
    V<T> v;
    ll tail=-1,cycle=0;
public:
    cyc_(){}
    T func(T x){
        x%=100;
        x++;
        if(x==100)x=0;
        return x;
    }
    void survey(T x){
        map<T,int>mp;
        while(!mp.count(x)){
            mp[x]=cycle++;
            v.push_back(x);
            x=func(x);
        }
        tail=mp[x];
        cycle-=tail;
    }
    T res(T x,ll n){
        if(tail==-1)survey(x);
        ll tm=min(n,tail);
        tm+=(n-tm)%cycle;
        return v[tm];
    }
};



// 累乗計算
ll pow_(ll x,ll n){
    if(n==0) return 1;
    if(n==1) return x;
    if(n%2==1) return x*pow_(x,n-1)%P;
    ll res=pow_(x,n/2);
    return res*res%P;
}

void MAIN(){
    int n, ans ;
    vi v;

    // permutation
    int perm_sz;
    vi perm(perm_sz);
    rep(i,0,perm_sz) perm[i]=i;
    do{
        rep(peri,0,sz(perm)){int i=peri;

        }
    }
    while(next_permutation(all(perm)));


// 尺取り
int r=0, now=0, lim;
rep(l,0,n){
    while(r<n && now+v[r]<=lim)now+=v[r++];
    ans+=(r-l);
    if(r==l)r++;
    else now-=v[l];
}

}


// 未完	   
/*
// 尺取り
  rep(l,0,n){
    while(r<n && now+v[r]<=x)now+=v[r++];
    ans+=(r-l);
    if(r==l)r++;
    else now-=v[l];
  }
*/

/*
//　素因数分解
  ll n;
  V<P> pf;
  for(ll p:prm){
    if(n%p==0){
      int now=0;
      while(n%p==0){
        n/=p;
        now++;
      }
      pf.pb(P(p,now));
    }
  }
  if(n!=1)pf.pb(P(n,1));
*/

/*
// LCA 最小共通祖先 ABC014D
int n;
vector<vi> dbl_par(20,vi(n,0)),to(n);
vi dep(n);
void dfs(int x,int par,int depth){ // dfs(0,-1,0); -> 深さをメモできればそれで良い
    dep[x]=depth;   // x の根からの深さをメモしていく
    for(int nx:to[x])
        if(nx!=par) dfs(nx,x,depth+1); // すべての頂点に対して行う
    return ;
}
int LCA(int x,int y){
    if(dep[x]<dep[y])swap(x,y); // より深い方をx とする

    for(int i=19;i>=0;i--)
 // LCA に漸近する、LCA==y (x の親をたどったときにy がいる)の場合にはx==y がかなう
        if((dep[x]-dep[y])>>i&1) x=dbl_par[i][x];

    if(x==y)return x;
 // 以下、x!=y である
    for(int i=19;i>=0;i--)
 // i==0 のときに特別処理を書くよりは、漸近させて最後に一つ上の頂点を返すほうがきれい　-> x==y　の場合はすでに弾かれている
        if(dbl_par[i][x] != dbl_par[i][y]){ // LCA の下端にまでx,y を進める
            x=dbl_par[i][x];
            y=dbl_par[i][y];
        }
    return dbl_par[0][x]; // 返すべきLCA は、x,y の一つ上の頂点に来ている
}
*/




/*
multiset<int> st;
// x wo hitotu dake kesu
st.erase(st.find(x));
*/



/*
// substring
// 2~5 (begin~end)
s.substr(2,6);

// 0-ind x~y
s.substr(x,y-x+1);
*/
/*
// erase -> i banme
v.erase(v.begin()+i);
*/
/*

/*
  bitset<8> bs(64);
  // bitset<8> bs("1000");

  if(bs[2]==1){}
  bs.set(3);
  // bs.reset(2);
*/


/*
// ｎ以下で、ｎと互いに素な数の個数
// オイラー関数
  ll n;
  ll res=n;
  for(auto x:pf){
    ll p=x.first;

    res*=(p-1);
    res/=p;
  }
*/

/*nCk　の全列挙
template<typename ite>
inline bool next_comb(const ite first,const ite last,int kk){
  ite k=first;
  while(kk--)k++;
  if(first==last or first==k or k==last)return 0;
  ite itr1=first;
  ite itr2=last;

  if(++itr1==last)return 0;
  itr1=k;
  itr2--;

  while(first!=itr1){
    if(*--itr1<*itr2){
      ite j=k;
      while(*itr1>=*j)++j;
      iter_swap(itr1++,j++);
      itr2=k;
      
      rotate(itr1,j,last);
      while(last!=j){
        j++;
        itr2++;
      }
      
      rotate(k,itr2,last);
      return 1;
    }
  }

  rotate(first,k,last);
  return 0;
}

int main(){
  cci(n,k);
  if(n<=k)return co(-1),0;
  vll v(n);
  iota(all(v),1);
  
  do{
    rep(i,0,k)cout<<v[i]<<" ";
    co("");
  }
  while(next_comb(all(v),k));
}
*/



/*
ll x,y;
ll exgcd(ll a,ll b,ll &x,ll &y){
  if(b==0){x=1;y=0;return a;}
  ll g=exgcd(b,a%b,y,x);
  y-=a/b*x;
  return g
}
// gcd(a,b)=1 の時、a*x==1(mod p)　よりx=a^(-1);
// これは　xが　mod pにおいて　aの逆元であることを表している
// 

*/