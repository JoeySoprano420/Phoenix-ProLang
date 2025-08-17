Here’s the **Type Space & Modes** add-on for Phoenix ProLang, answering “is it strong/explicit/dynamic,” and slotting cleanly into the spec.

# Type Space & Modes

## 1) Posture at a glance

* **Strength:** **Strongly typed.** No silent coercions; all conversions are explicit or rule-driven via validators/traits.
* **Timing:** **Statically typed by default** with **local type inference** (Hindley–Milner–style inference constrained by Phoenix traits/validators).
* **Dynamism:** **Gradual typing lane available** via `dynamic`/`any`/`reflect` with validator guards. Dynamic regions are opt-in and sandboxed.
* **Nullability:** **Non-nullable by default.** `null` is only legal for pointer-like and `option<T>`; otherwise use `option<T>` or `nullable<T>`.
* **Ownership:** Linear/affine semantics through `lease/sublease/release` with **lifetime inference** (no lifetime annotations in the surface syntax).

---

## 2) The Phoenix Type Space

### 2.1 Primitives

```
bool, byte, u16, u32, u64, i16, i32, i64, f32, f64, char, codepoint,
duration, index, size, checksum
```

* `bool` is 1-byte, truthy only if `true`.
* `duration` carries unit metadata (ns/µs/ms/s) at type level; arithmetic requires unit compatibility or explicit cast.
* `index`, `size` are platform-wide unsigned types (bounds-checked in validators when enabled).

### 2.2 Aggregates & algebraic types

* **Tuples:** `(T1, T2, …)`
* **Records/classes:** `class Point { x:i32; y:i32; }`
* **Arrays/packets:** `packet<T>[N]` (layout + alignment guaranteed)
* **Sum types / enums with data:**

  ```phoenix
  enum Result<T,E> { Ok(T), Err(E) }
  ```
* **Optionals:** `option<T>` (preferred over raw nullables)

### 2.3 Reference & pointer space

* **References:** `ref T` (non-owning, non-nullable)
* **Pointers:** `ptr T` (owning semantics via `lease`), can be `null`
* **Smart handles:** `smart<T>`, `unique<T>`, `shared<T>` (policies selectable)
* **Slices/views:** `view<T>` (fat pointer: ptr + length; no ownership)

### 2.4 Traits / Validators (typeclass-like)

* Constraints live as **traits** (compile-time) and **validators** (prove/run-time).

  * Examples: `Sized`, `Send`, `Sync`, `Aligned<N>`, `Checksum`.

  ```phoenix
  fn sum<T: Add + Zero>(xs: view<T>) -> T { ... }
  ```

### 2.5 Generics

* **Parametric polymorphism** with trait bounds:

  ```phoenix
  class Box<T: Sized + Send> { inner: T }
  fn swap<T>(a: ref T, b: ref T) { ... }
  ```

### 2.6 Effects & safety capsules

* **Capsules** annotate blocks with safety guarantees (no data races, bounds proven, etc.). These are **not** types but constrain the type checker’s allowed moves within a region.

---

## 3) Modes: Explicit, Inferred, Dynamic

### 3.1 Explicit typing (always available)

```phoenix
let n: i32 = 42;
let v: packet<f64>[1024] = aloc<packet<f64>[1024]>();
```

### 3.2 Local type inference (default ergonomic mode)

* `let` allows **inference** from the initializer:

  ```phoenix
  let z = 3.14;      // z: f64
  let p = Point{ x:1, y:2 }; // p: Point
  ```
* Inference is **local and deterministic**; no global backtracking.
* Overloads resolve only with sufficient type evidence; ambiguous calls require an **ascription**:

  ```phoenix
  let s = parse("5") : Result<i32, ParseErr>;
  ```

### 3.3 Gradual/dynamic typing (opt-in, fenced)

* **`dynamic`** holds any runtime value with a vtable-like tag; **`any`** is a compile-time erased carrier that becomes `dynamic` at boundaries.
* All dynamic use must go through **validator/trait checks** or **pattern matches**:

  ```phoenix
  let d: dynamic = json::parse(src);
  match d {
    as i: i64      => print(i+1),
    as s: string   => print(len(s)),
    _              => deny "unexpected type"
  }
  ```
* Crossing into `dynamic` **never** leaks into static regions without an explicit check/cast:

  ```phoenix
  let x: i32 = assume<int>(d) where validator is_i32(d);
  ```

---

## 4) Conversions & Coercions

### 4.1 Implicit (limited, safe, lossless only)

* `i32 → i64`, `f32 → f64`, `&T → view<T>` (when size known), `option<T> → option<U>` if `T→U` is implicit.
* **No** numeric narrowing, **no** bool↔int, **no** float→int implicit.

### 4.2 Explicit (spelled by you)

* `cast<T>(expr)` or postfix `: T` ascription:

  ```phoenix
  let x = cast<i16>(some_i64);
  let y = (3.0): f32;
  ```

### 4.3 Validator-mediated casts

* Require a named proof:

  ```phoenix
  let idx: index = cast_if<index>(n) where validator nonneg(n);
  ```

---

## 5) Nullability & Option Discipline

* Default fields/refs are **non-nullable**. To allow “absent,” use:

  * `option<T>` and match:

    ```phoenix
    let maybe: option<string> = none;
    match maybe { some(s) => print(s), none => print("empty") }
    ```
  * Or `nullable<T>` for interop, with stricter checks than `option<T>`.

---

## 6) Ownership, Lifetimes, and Aliasing

### 6.1 Lease/sublease (linear/affine core)

* `lease` creates **exclusive** ownership with a statically bounded lifetime (inferred to the block).
* `sublease` creates **shared, read-only** borrows with non-overlapping mutation.
* The compiler performs **lifetime inference** and **borrow checking**; no annotations needed in surface code.

```phoenix
lease buf = aloc<packet<byte>[1024]>();
{
  sublease head = buf[0..64];   // read view
  // write(buf) is illegal while `head` is alive unless proven disjoint
}
release buf;
```

### 6.2 Mutation gates

* Mutation of a leased object while any sublease exists is rejected unless:

  * The write is to a **proven disjoint** range (using range validators), or
  * All subleases are out of scope.

---

## 7) Overloading, Traits, and Inference

* Operator overloading is **trait-driven** (e.g., `Add`, `Mul`, `Eq`, `Ord`).
* Method resolution prefers **inherent impls**, then **trait impls** in scope.
* Inference picks the **most specific** candidate; ties require ascription.

```phoenix
trait Add<Rhs, Out> { fn add(self, rhs:Rhs) -> Out }
impl Add<i32,i32> for i32 { ... }
```

---

## 8) Compile-time Evaluation & Const

* `@consteval` functions evaluate at compile time; results are **typed constants**.
* `const` values participate in type-level arithmetic for sizes/alignments:

  ```phoenix
  const N: size = 1024;
  let b: packet<byte>[N];
  ```

---

## 9) Reflection & `typeof`

* `typeof(expr)` yields a fully resolved static type.
* `reflect<T>` exposes metadata (size, align, fields, traits satisfied) for **build-time macros**; not available at runtime unless `dynamic`.

---

## 10) Error Types & Exceptions

* Checked error algebra via `Result<T,E>` is preferred.
* `throw`/`try`/`catch` exist but **must declare** thrown types:

  ```phoenix
  fn risky() throws IoError { ... }
  try { risky(); } catch (e: IoError) { ... }
  ```
* The type system enforces catch coverage for declared throws.

---

## 11) EBNF snippets (types & binds)

```
Type        := SimpleType
            | Type "[" Expr "]"         // arrays/packets
            | "option" "<" Type ">"
            | "nullable" "<" Type ">"
            | "view" "<" Type ">"
            | "ptr"  "<" Type ">"
            | "ref"  "<" Type ">"
            | "(" Type ("," Type)+ ")"  // tuple
            | Ident "<" TypeList ">"    // generic

Binder      := ("let" | "lease" | "sublease") Ident (":" Type)? ("=" Expr)?
Ascription  := Expr ":" Type
Cast        := "cast" "<" Type ">" "(" Expr ")"
```

---

## 12) Quick contrasts (for clarity)

* **Strong vs Weak:** Phoenix is **strong**—no silent lossy conversions; validators gate risky moves.
* **Static vs Dynamic:** **Static by default** with **gradual dynamic pockets** (`dynamic`/`any`) behind explicit fences.
* **Explicit vs Inferred:** Both. Types are **explicit when you want**, **inferred when obvious**; ambiguity must be resolved by you.

---

## 13) Micro-examples

**Explicit & inferred mix**

```phoenix
let a = 1;              // i32
let b: i64 = a;         // explicit widening OK
let c: f32 = cast<f32>(b);
```

**Dynamic pocket with guard**

```phoenix
let d: dynamic = get_config();
if (is<int>(d)) {
  let n: i32 = assume<int>(d);
  print(n+1);
} else deny "config must be int";
```

**Ownership and options**

```phoenix
lease file = File("out.txt");           // wrapper + lease
let maybe_line: option<string> = file.read_line();
match maybe_line { some(s) => print(s), none => () }
release file;
```

---

---

# Phoenix ProLang — Unified Spec (v0.2)

## 1) Philosophy

Phoenix ProLang is a C++-inspired, **strongly typed**, **statically typed by default** language with **local type inference**, optional **gradual/dynamic pockets**, and **first-class parallelism**. Performance is king: zero-overhead abstractions, explicit control when wanted, and safety enforced by **capsules**, **validators**, and **ownership (lease/sublease)**.

## 2) Core Ideas (quick map)

* **Strong typing**: no silent lossy coercions; casts are explicit or validator-gated.
* **Static typing + inference**: local, deterministic inference; explicit types always available.
* **Gradual pockets**: `dynamic`/`any` fenced behind checks/matches.
* **Ownership model**: `lease` (exclusive), `sublease` (shared read view), `release` (end).
* **Capsules & validators**: region safety + proof obligations (bounds, alignment, checksum).
* **Packets & views**: `packet<T>[N]` (contiguous, aligned) and `view<T>` (fat slice).
* **Binders**: `let`, `lease`, `sublease`, destructuring, pattern guards.
* **Wrappers**: RAII shells (FFI, resources, concurrency).
* **Macros**: hygienic declarative + typed procedural, attribute macros, consteval stage.

## 3) Type Space & Modes

### 3.1 Primitives

`bool, byte, i16, i32, i64, u16, u32, u64, f32, f64, char, duration, index, size, checksum`

### 3.2 Aggregates & algebraic

* Tuples `(T1, T2, …)`
* `class` records
* `packet<T>[N]` (fixed length, ABI-stable)
* `enum`/sum types (e.g., `Result<T,E>`)
* `option<T>`; `nullable<T>` for interop

### 3.3 References & pointers

* `ref T` (non-owning, non-null)
* `ptr T` (pointer; can be `null`)
* `view<T>` (ptr+len; read-only by default)
* smart handles: `smart<T>`, `unique<T>`, `shared<T>`

### 3.4 Traits & validators

* Traits (compile-time): `Sized`, `Send`, `Add`, `Zero`, `Checksum`, `Aligned<N>`
* Validators (prove/run-time): e.g., `bounds(i,n)`, `nonneg(x)`

### 3.5 Modes

* **Explicit**: `let n: i32 = 42;`
* **Inferred**: `let z = 3.14; // f64`
* **Dynamic** (opt-in): `let d: dynamic = parse(json); match d { as i:i64 => …, … }`

### 3.6 Conversions

* **Implicit (lossless only)**: `i32→i64`, `f32→f64`, `&T→view<T>`
* **Explicit**: `cast<T>(expr)` or `expr : T`
* **Validator-gated**: `cast_if<index>(n) where validator nonneg(n)`

### 3.7 Nullability

Non-nullable by default; use `option<T>` (preferred) or `nullable<T>`.

### 3.8 Ownership & aliasing

* `lease` gives exclusive, affine ownership within a scope.
* `sublease` creates shared **read** views; mutation on the leased region is rejected while overlapping subleases exist (unless disjoint proven).
* Disjoint proof via range validators (e.g., `disjoint([a..b), [c..d))`).

## 4) Binders, Wrappers, Macros (essentials)

* **Binders**: `let`, `lease`, `sublease`, destructuring; generic/type binders with trait bounds; capability binders with `capsule uses(...)`.
* **Wrappers**: RAII resources (`init`/`drop`), validator wrappers (checked types), FFI wrappers with stamps, policy wrappers (arena/pinned).
* **Macros**: hygienic pattern macros, typed procedural macros, attribute macros (`@unroll(8)`, `@profile(hot)`), `@consteval` CT execution, metapackets, safety rails (no I/O unless `@build(allow_io)`).

## 5) Minimal EBNF slice

```
Binder      := ("let" | "lease" | "sublease") Ident (":" Type)? ("=" Expr)?
Type        := Prim
             | "packet" "<" Type ">" "[" Expr "]"
             | "view" "<" Type ">" | "ptr" "<" Type ">"
             | "option" "<" Type ">" | "nullable" "<" Type ">"
             | "(" Type ("," Type)+ ")" | Ident "<" TypeList ">"
Ascription  := Expr ":" Type
Cast        := "cast" "<" Type ">" "(" Expr ")"
```

---

# C++17 Prototype — Type+Trait Checker with Borrow Checking

Single file you can compile right away. It:

* Models **types**, **traits**, and a tiny **constraint solver**
* Tracks **lease/sublease** and **detects overlapping writes**
* Shows both an **error case** (illegal write while sublease exists) and a **legal case** (disjoint write)
* Demonstrates **trait-bound checking** for a generic `sum<T: Add+Zero>` call

**Build**

```bash
g++ -std=c++17 -O2 -Wall -Wextra phoenix_tc.cpp -o phoenix_tc
./phoenix_tc
```

```cpp
// phoenix_tc.cpp
// Phoenix ProLang — Minimal Type/Trait + Borrow Checker Prototype (C++17)
// Focus: strong/static typing posture, trait bounds, lease/sublease alias rules.

#include <bits/stdc++.h>
using namespace std;

// ---------- Utilities
struct Span { int line=0, col=0; };
struct Diag { string kind; string msg; Span where{}; };
struct Diags {
    vector<Diag> ds;
    void err(string m, Span s={}) { ds.push_back({"ERROR", move(m), s}); }
    void warn(string m, Span s={}){ ds.push_back({"WARN",  move(m), s}); }
    void info(string m, Span s={}){ ds.push_back({"INFO",  move(m), s}); }
    bool ok() const { return none_of(ds.begin(), ds.end(), [](auto& d){return d.kind=="ERROR";}); }
    void dump() const {
        for (auto& d: ds) cerr<<d.kind<<": "<<d.msg
                              <<(d.where.line?(" @"+to_string(d.where.line)+":"+to_string(d.where.col)):"")<<"\n";
    }
};

// ---------- Type system (very small but extensible)
enum class TKind { Prim, Packet, View, Ptr, Ref, Option, Dynamic, Tuple, Generic, Applied };
enum class Prim { Bool, Byte, I32, I64, F32, F64 };

struct Type {
    TKind k;
    Prim p{};                     // for Prim
    shared_ptr<Type> elem;        // for Packet/View/Ptr/Ref/Option
    size_t n = 0;                 // for Packet length
    string name;                  // for Generic/Applied
    vector<shared_ptr<Type>> args;// for Tuple/Applied

    static shared_ptr<Type> prim(Prim p){ auto t=make_shared<Type>(); t->k=TKind::Prim; t->p=p; return t; }
    static shared_ptr<Type> packet(shared_ptr<Type> el, size_t n) { auto t=make_shared<Type>(); t->k=TKind::Packet; t->elem=el; t->n=n; return t; }
    static shared_ptr<Type> view(shared_ptr<Type> el){ auto t=make_shared<Type>(); t->k=TKind::View; t->elem=el; return t; }
    static shared_ptr<Type> ptr (shared_ptr<Type> el){ auto t=make_shared<Type>(); t->k=TKind::Ptr;  t->elem=el; return t; }
    static shared_ptr<Type> ref (shared_ptr<Type> el){ auto t=make_shared<Type>(); t->k=TKind::Ref;  t->elem=el; return t; }
    static shared_ptr<Type> opt (shared_ptr<Type> el){ auto t=make_shared<Type>(); t->k=TKind::Option;t->elem=el; return t; }
    static shared_ptr<Type> dyn (){ auto t=make_shared<Type>(); t->k=TKind::Dynamic; return t; }
    static shared_ptr<Type> tuple(vector<shared_ptr<Type>> xs){ auto t=make_shared<Type>(); t->k=TKind::Tuple; t->args=move(xs); return t; }
    static shared_ptr<Type> generic(string n){ auto t=make_shared<Type>(); t->k=TKind::Generic; t->name=move(n); return t; }
    static shared_ptr<Type> applied(string n, vector<shared_ptr<Type>> xs){ auto t=make_shared<Type>(); t->k=TKind::Applied; t->name=move(n); t->args=move(xs); return t; }
};

static string primName(Prim p){
    switch(p){ case Prim::Bool: return "bool"; case Prim::Byte: return "byte";
               case Prim::I32: return "i32"; case Prim::I64: return "i64";
               case Prim::F32: return "f32"; case Prim::F64: return "f64"; }
    return "?";
}

static string show(shared_ptr<Type> t){
    switch(t->k){
        case TKind::Prim:   return primName(t->p);
        case TKind::Packet: return "packet<"+show(t->elem)+">["+to_string(t->n)+"]";
        case TKind::View:   return "view<"+show(t->elem)+">";
        case TKind::Ptr:    return "ptr<"+show(t->elem)+">";
        case TKind::Ref:    return "ref<"+show(t->elem)+">";
        case TKind::Option: return "option<"+show(t->elem)+">";
        case TKind::Dynamic:return "dynamic";
        case TKind::Tuple: {
            string s="("; for(size_t i=0;i<t->args.size();++i){ if(i) s+=", "; s+=show(t->args[i]); } s+=")"; return s;
        }
        case TKind::Generic:return t->name;
        case TKind::Applied:{
            string s=t->name+"<";
            for(size_t i=0;i<t->args.size();++i){ if(i) s+=", "; s+=show(t->args[i]); }
            s+=">";
            return s;
        }
    }
    return "?";
}
static bool eq(shared_ptr<Type> a, shared_ptr<Type> b){
    if (a->k!=b->k) return false;
    switch(a->k){
        case TKind::Prim:    return a->p==b->p;
        case TKind::Dynamic: return true;
        case TKind::Ptr:
        case TKind::Ref:
        case TKind::View:
        case TKind::Option:  return eq(a->elem,b->elem);
        case TKind::Packet:  return a->n==b->n && eq(a->elem,b->elem);
        case TKind::Tuple:   if(a->args.size()!=b->args.size()) return false;
                             for(size_t i=0;i<a->args.size();++i) if(!eq(a->args[i],b->args[i])) return false; return true;
        case TKind::Generic: return a->name==b->name;
        case TKind::Applied: if(a->name!=b->name || a->args.size()!=b->args.size()) return false;
                             for(size_t i=0;i<a->args.size();++i) if(!eq(a->args[i],b->args[i])) return false; return true;
    }
    return false;
}

// ---------- Trait registry & solver
struct Trait { string name; };
struct TraitDB {
    // fingerprint string -> traits it implements
    unordered_map<string, unordered_set<string>> ok;
    static string keyOf(shared_ptr<Type> t){ return show(t); } // crude but fine here
    void impl(shared_ptr<Type> t, string trait){ ok[keyOf(t)].insert(move(trait)); }
    bool has(shared_ptr<Type> t, string trait) const {
        auto it=ok.find(keyOf(t)); if(it==ok.end()) return false;
        return it->second.count(trait)>0;
    }
};

struct Bound { string trait; shared_ptr<Type> ty; };
struct Solver {
    const TraitDB& db; Diags& di;
    bool checkAll(const vector<Bound>& bs){
        bool good=true;
        for (auto& b: bs){
            if(!db.has(b.ty,b.trait)){
                di.err("Type "+show(b.ty)+" does not satisfy trait '"+b.trait+"'");
                good=false;
            }
        }
        return good;
    }
};

// ---------- Borrow checker (lease/sublease + ranges)
enum class BindKind { Let, Lease, Sublease };
struct Range { size_t lo, hi; }; // half-open [lo,hi)
static bool overlap(const Range&a, const Range&b){ return !(a.hi<=b.lo || b.hi<=a.lo); }

struct VarInfo {
    string name;
    BindKind kind;
    shared_ptr<Type> type;
    bool leased=false;          // for packet ownership
    vector<Range> subViews;     // active sublease ranges on the packet
};

struct Scope {
    unordered_map<string, VarInfo> vars;
    Scope* parent=nullptr;
    VarInfo* find(string n){ if(vars.count(n)) return &vars[n]; return parent?parent->find(n):nullptr; }
};

struct Checker {
    TraitDB& traits;
    Diags di;
    Scope root;

    // declarations
    bool decl(string name, BindKind k, shared_ptr<Type> ty){
        if(root.vars.count(name)){ di.err("Redeclaration of '"+name+"'"); return false; }
        VarInfo v{ name, k, ty, k==BindKind::Lease /*leased?*/, {} };
        root.vars.emplace(name, move(v));
        return true;
    }
    // sublease slice of packet
    bool subleaseView(string from, string viewName, Range r){
        auto* v = root.find(from);
        if(!v){ di.err("Unknown variable '"+from+"'"); return false; }
        if(v->type->k!=TKind::Packet){ di.err("Sublease requires packet<T>[N], got "+show(v->type)); return false; }
        // record active sublease
        v->subViews.push_back(r);
        // declare the view variable as a read-only view<T>
        auto viewT = Type::view(v->type->elem);
        return decl(viewName, BindKind::Sublease, viewT);
    }
    // write to a packet region
    bool writePacket(string to, Range r){
        auto* v = root.find(to);
        if(!v){ di.err("Unknown variable '"+to+"'"); return false; }
        if(v->kind!=BindKind::Lease){ di.err("Write requires exclusive lease of '"+to+"'"); return false; }
        if(v->type->k!=TKind::Packet){ di.err("Write target must be packet<T>[N], got "+show(v->type)); return false; }
        // bounds check (light)
        if(r.hi>v->type->n) di.err("Write range ["+to_string(r.lo)+","+to_string(r.hi)+") exceeds packet length "+to_string(v->type->n));
        // alias check vs active subleases
        for(auto& s : v->subViews){
            if(overlap(s,r)){
                di.err("Illegal write to '"+to+"' range ["+to_string(r.lo)+","+to_string(r.hi)+") "
                       "while sublease view is active over ["+to_string(s.lo)+","+to_string(s.hi)+")");
                return false;
            }
        }
        return true;
    }
    // release lease (ends exclusivity; clears subleases)
    void release(string name){
        auto* v = root.find(name);
        if(!v){ di.err("Unknown variable '"+name+"'"); return; }
        v->leased=false; v->subViews.clear();
    }
};

// ---------- Demo program assembly
int main(){
    // Types we will use
    auto i32  = Type::prim(Prim::I32);
    auto f64  = Type::prim(Prim::F64);
    auto byte = Type::prim(Prim::Byte);
    auto pBuf = Type::packet(byte, 1024);

    // Trait database with a couple of impls
    TraitDB traits;
    traits.impl(i32, "Add");
    traits.impl(i32, "Zero");
    traits.impl(f64, "Add");
    traits.impl(f64, "Zero");

    // Constraint solver demo: generic sum<T: Add + Zero>
    Diags di_traits;
    Solver solver{traits, di_traits};
    vector<Bound> needI32{{"Add", i32}, {"Zero", i32}};
    vector<Bound> needF64{{"Add", f64}, {"Zero", f64}};
    vector<Bound> needBad{{"Add", Type::dyn()}, {"Zero", Type::dyn()}};

    bool ok1 = solver.checkAll(needI32);
    bool ok2 = solver.checkAll(needF64);
    bool ok3 = solver.checkAll(needBad); // expected to fail (dynamic has no traits)
    if(!di_traits.ok()) di_traits.dump();
    cerr<<"Trait check (i32): "<<(ok1?"OK":"FAIL")<<"\n";
    cerr<<"Trait check (f64): "<<(ok2?"OK":"FAIL")<<"\n";
    cerr<<"Trait check (dyn): "<<(ok3?"OK":"FAIL")<<"\n\n";

    // Borrow checking demo
    Checker C{traits};

    // lease buf: packet<byte>[1024]
    C.decl("buf", BindKind::Lease, pBuf);

    // sublease head = buf[0..64)
    C.subleaseView("buf","head",{0,64});

    // Attempt illegal write inside active sublease range -> ERROR
    C.writePacket("buf",{10,12});

    // Legal disjoint write
    C.writePacket("buf",{128,256});

    // Release
    C.release("buf");

    if(!C.di.ok()){ C.di.dump(); cerr<<"\n"; }
    else cerr<<"No borrow errors.\n";

    // Summary
    cerr<<"Types: buf: "<<show(pBuf)<<", head: "<<show(Type::view(byte))<<"\n";
    return 0;
}
```

### What this prototype already proves

* **Strong/static** posture with explicit type modeling
* **Traits as constraints** + a small **solver** (see `Add`, `Zero`)
* **Lease/Sublease** semantics with a concrete **overlap check** on packet ranges
* Basic **diagnostics** that read like compiler errors

### What to add next (I can extend on request)

* A tiny **parser** for the Phoenix surface syntax (start with binders, slices, writes)
* **Range validators** as first-class proofs (e.g., `disjoint(a,b)` to allow concurrent writes by proof)
* **Capsules**: annotate a block and restrict allowed operations (e.g., `NetSafe`)
* **Attribute macros** that rewrite loops (`@unroll`, `@profile(hot)`) before checks
* A slightly richer **trait solver** (associated types, blanket impls)
* **Type inference** over more expression forms (binary ops, calls)

