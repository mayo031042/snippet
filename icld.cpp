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
vector<int> uf_par;
void uf_init(int sz){uf_par.resize(sz,-1);}
int uf_rt(int x){
    if(uf_par[x]<0)return x;
    return uf_par[x]=uf_rt(uf_par[x]);
}
int uf_unt(int x,int y=-1){
    if(y==-1)y=x;
    x=uf_rt(x),y=uf_rt(y);
    if(x==y)return -uf_par[x];
    if(uf_par[x]>uf_par[y])swap(x,y);
    uf_par[x]+=uf_par[y];
    uf_par[y]=x;
    return -uf_par[x];
}


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


// segment tree;
vector<int> seg_t;
int seg_sz = 1, seg_init_num;
int seg_func_init(int left,int right){
    return max(left,right); // 書き換え
}
int seg_content(int i){
    return seg_t[seg_sz+i-1];
}
void seg_all_init(const vector<int> &v){
    int vec_sz=v.size();
    while( seg_sz < vec_sz ) seg_sz <<= 1;
    seg_t.resize( seg_sz*2-1, seg_init_num );
    rep(i,0,vec_sz) seg_init(i,v[i]);
}
void seg_init(int index,int x=seg_init_num){ // seg_t[i] を　ｘで初期化
    int now = index+seg_sz-1;
    seg_t[now] = x;

    while(now){
        int par = (now-1)/2;
        int chi = par*2+1;
        if( now == chi ) chi++;

        seg_t[par]=seg_func_init( seg_t[now], seg_t[chi] );
        now=par;
    }
}
int seg_func(int a,int b,int now=0,int l=0,int r=seg_sz){
  if(a<=l && r<=b)return seg_t[now];
  if(r<=a || b<=l)return 0;

  int hf=(l+r)/2;
  int chi_l=seg_func(a,b,now*2+1,l,hf);
  int chi_r=seg_func(a,b,now*2+2,hf,r);

  return seg_func_init(chi_l,chi_r);
}


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