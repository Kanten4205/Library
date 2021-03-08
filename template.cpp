//長すぎにも程があるので程度というものを知れ
#include <cassert>
#include <cctype>
#include <cerrno>
#include <cfloat>
#include <ciso646>
#include <climits>
#include <clocale>
#include <cmath>
#include <csetjmp>
#include <csignal>
#include <cstdarg>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <ccomplex>
#include <cfenv>
#include <cinttypes>
#include <cstdalign>
#include <cstdbool>
#include <cstdint>
#include <ctgmath>
#include <cwchar>
#include <cwctype>
#include <algorithm>
#include <bitset>
#include <complex>
#include <deque>
#include <exception>
#include <fstream>
#include <functional>
#include <iomanip>
#include <ios>
#include <iosfwd>
#include <iostream>
#include <istream>
#include <iterator>
#include <limits>
#include <list>
#include <locale>
#include <map>
#include <memory>
#include <new>
#include <numeric>
#include <ostream>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <stdexcept>
#include <streambuf>
#include <string>
#include <typeinfo>
#include <utility>
#include <valarray>
#include <vector>
#include <array>
#include <atomic>
#include <chrono>
#include <condition_variable>
#include <forward_list>
#include <future>
#include <initializer_list>
#include <mutex>
#include <random>
#include <ratio>
#include <regex>
#include <scoped_allocator>
#include <system_error>
#include <thread>
#include <tuple>
#include <typeindex>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
using namespace std;
const long long MOD1 = 1000000007;
const long long MOD2 = 998244353;
#define logn long
#define lnog long
#define lgon long
#define itn int
typedef pair<long long, long long> P;
const long long INF = 1000000000000006;
//省略系
//string
//upper : S を全部大文字にする
string upper(string S) {
    transform(S.begin(), S.end(), S.begin(), ::toupper);
    return S;
}
//lower : S を全部小文字にする
string lower(string S) { // S の全文字を小文字にする. O(N)
    transform(S.begin(), S.end(), S.begin(), ::tolower);
    return S;
}
//len : S の長さを返す
long long len(string S) { // S の長さを取得（long long）. O(N)
    return (long long)S.size();
}
//count_str : S の中に ch がいくつ含まれているか
long long count_str(string S, char ch) { // S 内に文字 ch がいくつ存在するか. O(N)
    long long ans = 0;
    for (long long i = 0; i < len(S); i++) {
        ans += (S.at(i) == ch);
    }
    return ans;
}
//split : S を ch で区分けする
vector<string> split(string S, char ch) { //特定の文字 ch で S を分ける. O(N)
    string T;
    vector<string>A;
    for (long long i = 0; i < len(S); i++) {
        if (S[i] != ch) T.push_back(S[i]);
        else {
            A.push_back(T);
            T.clear();
        }
    }
    if (!T.empty()) A.push_back(T);
    return A;
}

//vector
//rep : A を N 回繰り返してくっつける
template <typename T>
vector<T> rep(vector<T>& A, long long N) {
    vector<T> B;
    for (long long i = 0; i < N; i++) {
        for (long long j = 0; j < A.size(); j++) {
            B.push_back(A[j]);
        }
    }
    return B;
}
//count_arr : A の中に key がいくつ含まれているか
template <typename T>
long long count_arr(vector<T>& A, T key) {
    long long ans = 0;
    for (long long i = 0; i < A.size(); i++) {
        ans += (A.at(i) == key);
    }
    return ans;
}
//join : A の各要素を ch で結合した文字列
template <typename Q>
string join(vector<Q>& A, char ch) {
    string S;
    for (long long i = 0; i < A.size(); i++) {
        string T = to_string(A.at(i));
        long long j = 0;
        while (j < T.size()) {
            S.push_back(T[j]);
            j++;
        }
        if (i != A.size() - 1) S.push_back(ch);
    }
    return S;
}
//sorted : A をソートした配列を返す
template<typename T>
vector<T> sorted(vector<T>& A) {
    sort(A.begin(), A.end());
    return A;
}
//reversed : A を反転させた配列を返す
template<typename T>
vector<T> reversed(vector<T>& A) {
    reverse(A.begin(), A.end());
    return A;
}
//max_arr : A の中の最大値を返す
template<typename T>
T max_arr(vector<T>& A) {
    long long num = -10000000000000007;
    for (long long i = 0; i < A.size(); i++) {
        if (A[i] > num) num = A[i];
    }
    return num;
}
//min_arr : A の中の最小値を返す
template<typename T>
T min_arr(vector<T>& A) {
    long long num = 10000000000000007;
    for (long long i = 0; i < A.size(); i++) {
        if (A[i] < num) num = A[i];
    }
    return num;
}

//Data stracture
//UnionFind
struct UnionFind {
    vector<long long> par, siz;

    //初期化
    UnionFind(long long N) : par(N, -1), siz(N, 1) {}

    //根を求める
    long long root(long long x) {
        if (par[x] == -1) return x; //x自身が根である
        else return par[x] = root(par[x]);
    }

    //x と y が同じグループに属するかどうか
    bool same(long long x, long long y) {
        return root(x) == root(y);
    }

    //x を含むグループと y を含むグループを併合
    bool unite(long long x, long long y) {
        //x, y をそれぞれ根まで移動
        x = root(x); y = root(y);

        //既に x と y が同グループに属するなら false
        if (x == y) return false;

        //union by size
        if (siz[x] < siz[y]) swap(x, y);

        //y を x の子にする
        par[y] = x;
        siz[x] += siz[y];
        return true;
    }

    //x を含むグループのサイズ
    long long size(long long x) {
        return siz[root(x)];
    }
    //連結成分の個数をカウント
    long long count() {
        long long ans = 0;
        for (long long i = 0; i < (long long)par.size(); i++) {
            ans += (root(i) == i);
        }
        return ans;
    }
};
//区間最小値を求めるセグ木
template <typename T>
struct RMQ {
    const T INF = 2147483647;
    int N; //number of leaves
    vector<T> dat; //perfect binary tree

    RMQ(int n_) : N(), dat(n_ * 4, INF) { //The number of leaves can be displayed by the formula, 2 ^ x.
        int x = 1;
        while (n_ > x) {
            x *= 2;
        }
        N = x;
    }

    void update(long long i, T x) {
        i += N - 1;
        dat.at(i) = x;
        while (i > 0) {
            i = (i - 1) / 2; //parent
            dat.at(i) = min(dat.at(i * 2 + 1), dat.at(i * 2 + 2));
        }
    }

    //the minimum element of [a, b)
    T query(long long a, long long b) {
        return query_sub(a, b, 0, 0, N);
    }
    T query_sub(long long a, long long b, long long k, long long l, long long r) {
        if (r <= a || b <= l) {
            return INF;
        }
        else if (a <= l && r <= b) {
            return dat.at(k);
        }
        else {
            T vl = query_sub(a, b, k * 2 + 1, l, (l + r) / 2);
            T vr = query_sub(a, b, k * 2 + 2, (l + r) / 2, r);
            return min(vl, vr);
        }
    }
};

//関数
//input_arr : 配列 A を入力
template <typename T>
void input_arr(vector<T>& A, long long N) {
    for (long long i = 0; i < N; i++) {
        cin >> A[i];
    }
}
//output_arr : 配列 A を出力
template <typename T>
void output_arr(vector<T>& A, long long N) {
    for (long long i = 0; i < N; i++) {
        cout << A[i];
        if (i != N - 1) cout << ' ';
    }
    cout << endl;
}
//GCD : GCD
long long GCD(long long A, long long B) { return(B == 0 ? A : GCD(B, A % B)); }
//LCM : LCM
long long LCM(long long A, long long B) { return A / GCD(A, B) * B; }
//find : A 内に key のある位置（ないなら -1 ）
template <typename T>
long long find(vector<T>& A, T key) {
    long long left = 0, right = A.size() - 1;
    while (left <= right) {
        long long mid = (left + right) / 2;
        if (A[mid] == key) return mid;
        else if (A[mid] < key) left = mid + 1;
        else right = mid - 1;
    }
    return -1;
}
//elements : Aに含まれる要素は何種類か
template <typename T>
long long elements(vector<T>& A) {
    sort(A.begin(), A.end());
    long long ans = 1;
    for (long long i = 1; i < A.size(); i++) {
        if (A[i] != A[i - 1]) ans++;
    }
    return ans;
}
//prime_factorization : 素因数分解
vector<P> prime_factorization(long long N) {
    vector<P>A;
    long long tmp = N;
    for (long long i = 2; i * i <= N; i++) {
        if (tmp % i == 0) {
            A.push_back({ i, 0 });
            while (tmp % i == 0) {
                A.back().second++;
                tmp /= i;
            }
        }
    }
    if (tmp != 1) A.push_back({ tmp, 1 });
    return A;
}
//power : M^N(mod MOD)
long long power(long long M, long long N, long long MOD) {
    long long ans = 1;
    while (N > 0) {
        if (N & 1) {
            ans = ans * M % MOD;
        }
        M = M * M % MOD;
        N >>= 1;
    }
    return ans;
}
//Euler_phi : オイラー関数
long long Euler_phi(long long N) {
    vector<P>A = prime_factorization(N);
    for (long long i = 0; i < A.size(); i++) {
        N /= A[i].first;
    }
    for (long long i = 0; i < A.size(); i++) {
        N *= (A[i].first - 1);
    }
    return N;
}
//extgcd : 拡張ユークリッド互除法（返すのは gcd(A,B),AX + BY = GCD(A,B)）
long long extgcd(long long A, long long B, long long& X, long long& Y) {
    long long D = A;
    if (B != 0) {
        D = extgcd(B, A % B, Y, X);
        Y -= (A / B) * X;
    }
    else {
        X = 1; Y = 0;
    }
    return D;
}

//計算幾何
#define EPS (1e-10)
#define equals(a, b) (fabs((a) - (b)) < EPS)
//Point : 点(x, y)(点の座標(x,y)、ベクトル演算(+,-,*,/)、ベクトルのノルム(norm)、大きさ(abs)、大小比較(<)、合同を保存(==))
class Point {
public:
    double x;
    double y;

    Point(double x = 0, double y = 0) : x(x), y(y) {}

    Point operator+(Point p) { return Point(x + p.x, y + p.y); }
    Point operator-(Point p) { return Point(x - p.x, y - p.y); }
    Point operator*(double a) { return Point(a * x, a * y); }
    Point operator/(double a) { return Point(x / a, y / a); }

    double abs() { return sqrt(norm()); }
    double norm() { return x * x + y * y; }

    bool operator<(const Point& p) const {
        return x != p.x ? x < p.x : y < p.y;
    }
    bool operator==(const Point& p) const {
        return fabs(x - p.x) < (1e-10) && fabs(y - p.y) < (1e-10);
    }
};
//Vector : ベクトル（配列のvectorと間違えぬように）
typedef Point Vector;
//Segment : 線分AB(点A, Bの座標を保存)
struct Segment {
    Point A;
    Point B;
};
//Line : 直線AB
typedef Segment Line;
//Circle : 円(中心点C、半径r を保存)
class Circle {
public:
    Point C;
    double r;
    Circle(Point C = Point(), double r = 0.0) : C(C), r(r) {}
};
//Polygon : 多角形（各頂点の点列で表す）
typedef vector<Point> Polygon;
//dot : ベクトルA, B の内積
double dot(Vector A, Vector B) {
    return A.x * B.x + A.y * B.y;
}
//cross : ベクトルA, B の外積
double cross(Vector A, Vector B) {
    return A.x * B.y - A.y * B.x;
}
//Projection : 射影(点pを通る、直線Sへの垂線の足の座標)
Point Projection(Segment S, Point p) {
    Vector base = S.B - S.A;
    double r = dot(p - S.A, base) / base.norm();
    return S.A + base * r;
}
//Reflection : 反射(直線Sに関して、点pと対称な点の座標)
Point Reflection(Segment S, Point p) {
    return p + (Projection(S, p) - p) * 2.0;
}
//isOrthogonal : 直交しているか？ <==> ベクトルA, B の内積は0か？
bool isOrthogonal(Vector A, Vector B) {
    return equals(dot(A, B), 0.0);
}
bool isOrthogonal(Point A1, Point A2, Point B1, Point B2) {
    return isOrthogonal(A1 - A2, B1 - B2);
}
bool isOrthogonal(Segment S1, Segment S2) {
    return equals(dot(S1.B - S1.A, S2.B - S2.A), 0.0);
}
//isParallel : 平行か？ <==> ベクトルA, B の外積は0か？
bool isParallel(Vector A, Vector B) {
    return equals(cross(A, B), 0.0);
}
bool isParallel(Point A1, Point A2, Point B1, Point B2) {
    return isParallel(A1 - A2, B1 - B2);
}
bool isParallel(Segment S1, Segment S2) {
    return equals(cross(S1.B - S1.A, S2.B - S2.A), 0.0);
}
//getDistance : 2点A,Bの距離
double getDistance(Point A, Point B) {
    return (A - B).abs();
}
//getDistanceLP : 直線Lと点Pの距離
double getDistanceLP(Line L, Point P) {
    return abs((cross(L.B - L.A, P - L.A))) / (L.B - L.A).abs();
}
//getDistanceSP : 線分Sと点Pの距離
double getDistanceSP(Segment S, Point P) {
    if (dot(S.B - S.A, P - S.A) < 0.0) return (P - S.A).abs();
    if (dot(S.A - S.B, P - S.B) < 0.0) return (P - S.B).abs();
    return getDistanceLP(S, P);
}
//定数定義
static const int COUNTER_CLOCKWISE = 1;
static const int CLOCKWISE = -1;
static const int ONLINE_BACK = 2;
static const int ONLINE_FRONT = -2;
static const int ON_SEGMENT = 0;
//ccw : 3点A,B,Cがこの順に反時計回りか？
int ccw(Point A, Point B, Point C) {
    Vector S = B - A, T = C - A;
    if (cross(S, T) > EPS) return COUNTER_CLOCKWISE; //反時計回り
    if (cross(S, T) < -EPS) return CLOCKWISE; //時計回り
    if (dot(S, T) < -EPS) return ONLINE_BACK; //C,A,Bの順で同一直線上にある
    if (S.norm() < T.norm()) return ONLINE_FRONT; //A,B,Cの順で同一直線上にある
    return ON_SEGMENT; //Cが線分AB上にある
}
//intersect : 線分AB, CDは交差するか？
bool intersect(Point A, Point B, Point C, Point D) {
    return (ccw(A, B, C) * ccw(A, B, D) <= 0 && ccw(C, D, A) * ccw(C, D, B) <= 0);
}
bool intersect(Segment S1, Segment S2) {
    return intersect(S1.A, S1.B, S2.A, S2.B);
}
//getDistance : 線分S1, S2 の距離もこの関数で導入
double getDistance(Segment S1, Segment S2) {
    if (intersect(S1, S2)) return 0.0;
    return min(min(getDistanceSP(S1, S2.A), getDistanceSP(S1, S2.B)), min(getDistanceSP(S2, S1.A), getDistanceSP(S2, S1.B)));
}
