#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <fstream>
#include <iostream>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>
#include <string>
#include <system_error>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace std;
using namespace llvm;

// Error reporting
[[noreturn]] void reportError(const string& message, size_t line_number,
                              raw_ostream* OS = &errs()) {
    *OS << std::format("Error on line {}: {}\n", line_number, message);
    exit(1);
}

// String utilities
static inline string rtrim_cr(string s) {
    if (!s.empty() && (s.back() == '\r' || s.back() == '\n')) {
        while (!s.empty() && (s.back() == '\r' || s.back() == '\n'))
            s.pop_back();
    }
    return s;
}

static inline string trim(const string& s) {
    size_t i = 0, j = s.size();
    while (i < j && isspace(static_cast<unsigned char>(s[i])))
        ++i;
    while (j > i && isspace(static_cast<unsigned char>(s[j - 1])))
        --j;
    return s.substr(i, j - i);
}

static inline bool starts_with(const string& s, const string& p) {
    return s.size() >= p.size() && s.compare(0, p.size(), p) == 0;
}

static inline string remove_spaces(const string& s) {
    string t;
    t.reserve(s.size());
    for (unsigned char c : s)
        if (!isspace(static_cast<unsigned char>(c)))
            t.push_back(c);
    return t;
}

// AST
enum CmpOp { LT, GT, LE, GE, EQ, NE };

struct Stmt {
    enum Type { YOSORO, SET, IHU, HOR, WHILE_ } type;
    // YOSORO: print
    // SET: assign
    // IHU: if
    // HOR: for
    // WHILE_: while

    // YOSORO
    string expr;

    // SET
    string lhsName;
    bool lhsIsArray = false;
    string lhsIndexExpr;
    string rhsExpr;

    // IF / WHILE
    CmpOp op;
    string condA, condB;
    vector<Stmt> body;

    // FOR
    string forVarName;
    bool forVarIsArray = false;
    string forVarIndexExpr;
    string forStart, forEnd;
};

// Parsing
vector<string> gLines;
size_t gPosLine = 0;

vector<Stmt> parse_block(); // forward

vector<string> split_by_commas_no_space(const string& s,
                                        [[maybe_unused]] size_t expectedParts) {
    vector<string> parts;
    size_t i = 0, n = s.size();
    size_t last = 0;
    while (i <= n) {
        if (i == n || s[i] == ',') {
            parts.push_back(s.substr(last, i - last));
            last = i + 1;
        }
        ++i;
    }
    // assert(expectedParts == 0 || expectedParts == parts.size());
    return parts;
}

CmpOp parse_op(const string& s, size_t line_num) {
    if (s == "lt")
        return LT;
    if (s == "gt")
        return GT;
    if (s == "le")
        return LE;
    if (s == "ge")
        return GE;
    if (s == "eq")
        return EQ;
    if (s == "neq")
        return NE;
    reportError(std::format("Invalid comparison operator '{}'", s), line_num);
}

Stmt parse_stmt_one() {
    size_t currentLine = gPosLine + 1;
    string raw = rtrim_cr(gLines[gPosLine]);
    string t = trim(raw);
    ++gPosLine;
    Stmt s{};
    if (starts_with(t, ":yosoro")) {
        string rest = trim(t.substr(7));
        s.type = Stmt::YOSORO;
        s.expr = rest;
    } else if (starts_with(t, ":set")) {
        string rest = trim(t.substr(4));
        string rs = remove_spaces(rest);
        auto parts = split_by_commas_no_space(rs, 2);
        if (parts.size() != 2)
            reportError(
                "Invalid ':set' statement. Expected ':set <lhs>, <rhs>'.",
                currentLine);

        string lhs = parts[0];
        string rhs = parts[1];

        if (lhs.empty())
            reportError("Missing left-hand side in ':set' statement.",
                        currentLine);
        if (rhs.empty())
            reportError("Missing right-hand side in ':set' statement.",
                        currentLine);

        s.type = Stmt::SET;
        size_t lb = lhs.find('[');
        if (lb == string::npos) {
            s.lhsName = lhs;
            s.lhsIsArray = false;
        } else {
            s.lhsName = lhs.substr(0, lb);
            size_t rb = lhs.rfind(']');
            if (rb == string::npos || rb <= lb)
                reportError("Mismatched brackets in array access.",
                            currentLine);
            s.lhsIsArray = true;
            s.lhsIndexExpr = lhs.substr(lb + 1, rb - lb - 1);
            if (s.lhsIndexExpr.empty())
                reportError("Empty index in array access.", currentLine);
        }
        s.rhsExpr = rhs;
    } else {
        reportError(std::format("Unknown statement: {}", t), currentLine);
    }
    return s;
}

vector<Stmt> parse_block() {
    vector<Stmt> body;
    while (gPosLine < gLines.size()) {
        size_t currentLine = gPosLine + 1;
        string raw = rtrim_cr(gLines[gPosLine]);
        string t = trim(raw);
        if (t.empty()) {
            ++gPosLine;
            continue;
        }
        if (t == "}") {
            ++gPosLine;
            break;
        }

        if (t[0] == '{') {
            string hdr = trim(t.substr(1));
            if (starts_with(hdr, "ihu")) {
                string rest = trim(hdr.substr(3));
                string rs = remove_spaces(rest);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError("Invalid 'ihu' statement. Expected '{ihu <op>, "
                                "<expr1>, <expr2>}'.",
                                currentLine);
                Stmt s;
                s.type = Stmt::IHU;
                s.op = parse_op(parts[0], currentLine);
                s.condA = parts[1];
                s.condB = parts[2];
                ++gPosLine;
                s.body = parse_block();
                body.push_back(std::move(s));
            } else if (starts_with(hdr, "hor")) {
                string rest = trim(hdr.substr(3));
                string rs = remove_spaces(rest);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError("Invalid 'hor' statement. Expected '{hor "
                                "<var>, <start>, "
                                "<end>}'.",
                                currentLine);
                Stmt s{};
                s.type = Stmt::HOR;
                string forVarLhs = parts[0];
                size_t lb = forVarLhs.find('[');
                if (lb == string::npos) {
                    s.forVarName = forVarLhs;
                } else {
                    s.forVarName = forVarLhs.substr(0, lb);
                    size_t rb = forVarLhs.rfind(']');
                    if (rb == string::npos || rb <= lb)
                        reportError("Mismatched brackets in for loop variable.",
                                    currentLine);
                    s.forVarIsArray = true;
                    s.forVarIndexExpr = forVarLhs.substr(lb + 1, rb - lb - 1);
                    if (s.forVarIndexExpr.empty())
                        reportError("Empty index in for loop variable.",
                                    currentLine);
                }
                s.forStart = parts[1];
                s.forEnd = parts[2];
                ++gPosLine;
                s.body = parse_block();
                body.push_back(std::move(s));
            } else if (starts_with(hdr, "while")) {
                string rest = trim(hdr.substr(5));
                string rs = remove_spaces(rest);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError(
                        "Invalid 'while' statement. Expected '{while <op>, "
                        "<expr1>, <expr2>}'.",
                        currentLine);
                Stmt s;
                s.type = Stmt::WHILE_;
                s.op = parse_op(parts[0], currentLine);
                s.condA = parts[1];
                s.condB = parts[2];
                ++gPosLine;
                s.body = parse_block();
                body.push_back(std::move(s));
            } else if (starts_with(hdr, "vars")) {
                ++gPosLine;
                while (gPosLine < gLines.size()) {
                    string u = trim(rtrim_cr(gLines[gPosLine]));
                    ++gPosLine;
                    if (u == "}")
                        break;
                }
            } else {
                ++gPosLine; // unknown
                reportError(
                    std::format("Unknown block type starting with '{}'", hdr),
                    currentLine);
            }
        } else {
            Stmt s = parse_stmt_one();
            if (s.type == Stmt::YOSORO || s.type == Stmt::SET)
                body.push_back(std::move(s));
        }
    }
    return body;
}

// Vars block
struct VarDecl {
    string name;
    bool isArray = false;
    int64_t L = 0, R = -1;
};

vector<VarDecl> parse_vars_block(vector<string>& lines, size_t& pos) {
    vector<VarDecl> decls;
    while (pos < lines.size()) {
        string t = trim(rtrim_cr(lines[pos]));
        if (t.empty()) {
            ++pos;
            continue;
        }
        if (t.size() && t[0] == '{') {
            string hdr = trim(t.substr(1));
            if (starts_with(hdr, "vars")) {
                ++pos;
                while (pos < lines.size()) {
                    size_t varLine = pos + 1;
                    string raw = rtrim_cr(lines[pos]);
                    string s = trim(raw);
                    ++pos;
                    if (s == "}")
                        break;
                    if (s.empty())
                        continue;
                    string u = remove_spaces(s);
                    size_t colon = u.find(':');
                    if (colon == string::npos)
                        reportError("Invalid variable declaration. Expected "
                                    "'<name>:<type>'.",
                                    varLine);
                    string name = u.substr(0, colon);
                    string kind = u.substr(colon + 1);
                    VarDecl vd;
                    vd.name = name;
                    if (kind == "int") {
                        vd.isArray = false;
                    } else {
                        const string prefix = "array[int,";
                        if (starts_with(kind, prefix) && !kind.empty() &&
                            kind.back() == ']') {
                            string inside = kind.substr(
                                prefix.size(), kind.size() - prefix.size() - 1);
                            size_t dots = inside.find("..");
                            if (dots == string::npos)
                                reportError(
                                    "Invalid array range in declaration. "
                                    "Expected 'L..R'.",
                                    varLine);
                            string lstr = inside.substr(0, dots);
                            string rstr = inside.substr(dots + 2);
                            auto parse_int = [&](const string& str) -> int64_t {
                                if (str.empty())
                                    reportError("Empty number in array range.",
                                                varLine);
                                int32_t sign = 1;
                                size_t i = 0;
                                if (str[0] == '+') {
                                    sign = 1;
                                    i = 1;
                                } else if (str[0] == '-') {
                                    sign = -1;
                                    i = 1;
                                }
                                if (i == str.size())
                                    reportError(
                                        std::format(
                                            "Invalid number in array range: {}",
                                            str),
                                        varLine);
                                int64_t v = 0;
                                for (; i < str.size(); ++i) {
                                    if (!isdigit(
                                            static_cast<unsigned char>(str[i])))
                                        reportError(
                                            std::format("Invalid number in "
                                                        "array range: {}",
                                                        str),
                                            varLine);
                                    v = v * 10 + (str[i] - '0');
                                }
                                return sign * v;
                            };
                            vd.isArray = true;
                            vd.L = parse_int(lstr);
                            vd.R = parse_int(rstr);
                        } else {
                            reportError(
                                std::format("Invalid type '{}'. Expected 'int' "
                                            "or 'array[int,L..R]'.",
                                            kind),
                                varLine);
                        }
                    }
                    decls.push_back(std::move(vd));
                }
            }
        }
        break;
    }
    return decls;
}

vector<Stmt> parse_program_rest() {
    vector<Stmt> rest;
    while (gPosLine < gLines.size()) {
        size_t currentLine = gPosLine + 1;
        string raw = rtrim_cr(gLines[gPosLine]);
        string t = trim(raw);
        if (t.empty()) {
            ++gPosLine;
            continue;
        }
        if (t == "}") {
            ++gPosLine;
            continue;
        }
        if (t[0] == '{') {
            string hdr = trim(t.substr(1));
            if (starts_with(hdr, "ihu")) {
                string restStr = trim(hdr.substr(3));
                string rs = remove_spaces(restStr);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError("Invalid 'ihu' statement. Expected '{ihu <op>, "
                                "<expr1>, <expr2>}'.",
                                currentLine);
                Stmt s;
                s.type = Stmt::IHU;
                s.op = parse_op(parts[0], currentLine);
                s.condA = parts[1];
                s.condB = parts[2];
                ++gPosLine;
                s.body = parse_block();
                rest.push_back(std::move(s));
            } else if (starts_with(hdr, "hor")) {
                string restStr = trim(hdr.substr(3));
                string rs = remove_spaces(restStr);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError("Invalid 'hor' statement. Expected '{hor "
                                "<var>, <start>, <end>}'.",
                                currentLine);
                Stmt s{};
                s.type = Stmt::HOR;
                string forVarLhs = parts[0];
                size_t lb = forVarLhs.find('[');
                if (lb == string::npos) {
                    s.forVarName = forVarLhs;
                } else {
                    s.forVarName = forVarLhs.substr(0, lb);
                    size_t rb = forVarLhs.rfind(']');
                    if (rb == string::npos || rb <= lb)
                        reportError("Mismatched brackets in for loop variable.",
                                    currentLine);
                    s.forVarIsArray = true;
                    s.forVarIndexExpr = forVarLhs.substr(lb + 1, rb - lb - 1);
                    if (s.forVarIndexExpr.empty())
                        reportError("Empty index in for loop variable.",
                                    currentLine);
                }
                s.forStart = parts[1];
                s.forEnd = parts[2];
                ++gPosLine;
                s.body = parse_block();
                rest.push_back(std::move(s));
            } else if (starts_with(hdr, "while")) {
                string restStr = trim(hdr.substr(5));
                string rs = remove_spaces(restStr);
                auto parts = split_by_commas_no_space(rs, 3);
                if (parts.size() != 3)
                    reportError(
                        "Invalid 'while' statement. Expected '{while <op>, "
                        "<expr1>, <expr2>}'.",
                        currentLine);
                Stmt s;
                s.type = Stmt::WHILE_;
                s.op = parse_op(parts[0], currentLine);
                s.condA = parts[1];
                s.condB = parts[2];
                ++gPosLine;
                s.body = parse_block();
                rest.push_back(std::move(s));
            } else if (starts_with(hdr, "vars")) {
                ++gPosLine;
                while (gPosLine < gLines.size()) {
                    string u = trim(rtrim_cr(gLines[gPosLine]));
                    ++gPosLine;
                    if (u == "}")
                        break;
                }
            } else {
                ++gPosLine;
                reportError(
                    std::format("Unknown block type starting with '{}'", hdr),
                    currentLine);
            }
        } else {
            Stmt s = parse_stmt_one();
            if (s.type == Stmt::YOSORO || s.type == Stmt::SET)
                rest.push_back(std::move(s));
        }
    }
    return rest;
}

// Codegen symbols and helpers
struct Sym {
    bool isArray = false;
    AllocaInst* allocaInst = nullptr; // i64 or [N x i64]
    int64_t L = 0, R = -1;            // for arrays
    ArrayType* arrTy = nullptr;       // for arrays
};

struct CodeGenCtx {
    LLVMContext Ctx;
    unique_ptr<Module> Mod;
    IRBuilder<> Builder;
    IRBuilder<> AllocaBuilder;
    Function* MainFn = nullptr;
    BasicBlock* EntryBB = nullptr;

    // External functions
    FunctionCallee Printf;
    FunctionCallee Putchar;

    // Symbol table
    unordered_map<string, Sym> SymbolTable;

    // Types and constants
    Type* I64;
    Type* I32;
    Type* I8;
    Value* C0_64;
    Value* C1_64;
    Value* C10_32;

    CodeGenCtx(const string& moduleName)
        : Mod(make_unique<Module>(moduleName, Ctx)), Builder(Ctx),
          AllocaBuilder(Ctx) {
        I64 = Type::getInt64Ty(Ctx);
        I32 = Type::getInt32Ty(Ctx);
        I8 = Type::getInt8Ty(Ctx);
        C0_64 = ConstantInt::get(I64, 0);
        C1_64 = ConstantInt::get(I64, 1);
        C10_32 = ConstantInt::get(I32, 10); // '\n'

        // main
        FunctionType* FT = FunctionType::get(I32, false);
        MainFn =
            Function::Create(FT, Function::ExternalLinkage, "main", Mod.get());
        EntryBB = BasicBlock::Create(Ctx, "entry", MainFn);
        Builder.SetInsertPoint(EntryBB);
        AllocaBuilder.SetInsertPoint(EntryBB, EntryBB->begin());

        // extern printf / putchar
        Printf = Mod->getOrInsertFunction(
            "printf", FunctionType::get(I32, PointerType::getUnqual(I8), true));
        Putchar = Mod->getOrInsertFunction("putchar",
                                           FunctionType::get(I32, I32, false));
    }

    Value* emitPrintI64(Value* v) {
        auto* gv = Builder.CreateGlobalString("%lld ", "fmt");
        Value* idx0 = ConstantInt::get(I64, 0);
        Value* fmtPtr = Builder.CreateInBoundsGEP(
            gv->getValueType(), gv, ArrayRef<Value*>{idx0, idx0}, "fmt.ptr");
        return Builder.CreateCall(Printf, {fmtPtr, v});
    }

    void emitNewline() { Builder.CreateCall(Putchar, {C10_32}); }

    void declareVar(const VarDecl& vd) {
        if (!vd.isArray) {
            AllocaInst* A = AllocaBuilder.CreateAlloca(I64, nullptr, vd.name);
            Builder.CreateStore(C0_64, A); // Variables are initialized to 0
            Sym s;
            s.isArray = false;
            s.allocaInst = A;
            SymbolTable[vd.name] = s;
        } else {
            int64_t L = vd.L, R = vd.R;
            int64_t N = (R >= L) ? (R - L + 1) : 0;
            if (N <= 0)
                N = 1; // avoid zero-sized alloca
            ArrayType* AT = ArrayType::get(I64, (uint64_t)N);
            AllocaInst* A = AllocaBuilder.CreateAlloca(AT, nullptr, vd.name);
            Constant* ZeroArr = ConstantAggregateZero::get(AT);
            Builder.CreateStore(ZeroArr, A);

            Sym s;
            s.isArray = true;
            s.allocaInst = A;
            s.L = vd.L;
            s.R = vd.R;
            s.arrTy = AT;
            SymbolTable[vd.name] = s;
        }
    }

    Value* loadScalar(const string& name) {
        auto it = SymbolTable.find(name);
        assert(it != SymbolTable.end() && !it->second.isArray);
        return Builder.CreateLoad(I64, it->second.allocaInst,
                                  std::format("{}.val", name));
    }

    Value* getArrayElemPtr(const string& name, Value* idxVal) {
        auto it = SymbolTable.find(name);
        assert(it != SymbolTable.end() && it->second.isArray);
        Sym& s = it->second;
        Value* Lconst = ConstantInt::get(I64, s.L);
        Value* rel =
            Builder.CreateSub(idxVal, Lconst, std::format("{}.relidx", name));

        Value* zero = C0_64;
        Value* ptr0 = Builder.CreateInBoundsGEP(
            s.arrTy, s.allocaInst, {zero, zero}, std::format("{}.ptr0", name));

        Value* elemPtr = Builder.CreateInBoundsGEP(
            I64, ptr0, rel, std::format("{}.elemptr", name));
        return elemPtr;
    }

    Value* loadArrayElem(const string& name, Value* idxVal) {
        Value* elemPtr = getArrayElemPtr(name, idxVal);
        return Builder.CreateLoad(I64, elemPtr, std::format("{}.elem", name));
    }

    void storeScalar(const string& name, Value* v) {
        auto it = SymbolTable.find(name);
        assert(it != SymbolTable.end() && !it->second.isArray);
        Builder.CreateStore(v, it->second.allocaInst);
    }

    void storeArrayElem(const string& name, Value* idxVal, Value* v) {
        Value* elemPtr = getArrayElemPtr(name, idxVal);
        Builder.CreateStore(v, elemPtr);
    }
};

// Expression codegen
Value* buildExprString(CodeGenCtx& CG, const string& s, bool allowArray);

Value* buildExprCore(CodeGenCtx& CG, const string& t, bool allowArray) {
    Type* I64 = CG.I64;
    IRBuilder<>& B = CG.Builder;

    size_t i = 0, n = t.size();
    Value* res = nullptr;
    int32_t sign = +1;

    auto applySignAndAcc = [&](Value* term) {
        if (sign == -1) {
            term = B.CreateSub(ConstantInt::get(I64, 0), term, "negtmp");
        }
        if (!res)
            res = term;
        else
            res = B.CreateAdd(res, term, "addtmp");
        sign = +1;
    };

    while (i < n) {
        if (t[i] == '+') {
            sign = +1;
            ++i;
            continue;
        }
        if (t[i] == '-') {
            sign = -1;
            ++i;
            continue;
        }

        if (i >= n)
            break;

        if (isdigit(static_cast<unsigned char>(t[i]))) {
            int64_t v = 0;
            while (i < n && isdigit(static_cast<unsigned char>(t[i]))) {
                v = v * 10 + (t[i] - '0');
                ++i;
            }
            Value* term = ConstantInt::get(I64, v);
            applySignAndAcc(term);
        } else if (isalpha(static_cast<unsigned char>(t[i]))) {
            string name;
            while (i < n && isalpha(static_cast<unsigned char>(t[i]))) {
                name.push_back(t[i]);
                ++i;
            }

            if (i < n && t[i] == '[') {
                if (!allowArray) {
                    int32_t depth = 0;
                    do {
                        if (t[i] == '[')
                            ++depth;
                        else if (t[i] == ']')
                            --depth;
                        ++i;
                    } while (i < n && depth > 0);
                    applySignAndAcc(ConstantInt::get(I64, 0));
                } else {
                    size_t start = i + 1;
                    int32_t depth = 1;
                    size_t j = start;
                    while (j < n && depth > 0) {
                        if (t[j] == '[')
                            ++depth;
                        else if (t[j] == ']')
                            --depth;
                        ++j;
                    }
                    size_t end = j - 1;
                    string inside = t.substr(start, end - start);
                    Value* idxVal = buildExprString(CG, inside, false);
                    i = j;
                    Value* term = CG.loadArrayElem(name, idxVal);
                    applySignAndAcc(term);
                }
            } else {
                Value* term = CG.loadScalar(name);
                applySignAndAcc(term);
            }
        } else {
            ++i;
        }
    }
    if (!res)
        res = ConstantInt::get(I64, 0);
    return res;
}

Value* buildExprString(CodeGenCtx& CG, const string& s, bool allowArray) {
    string t = remove_spaces(s);
    return buildExprCore(CG, t, allowArray);
}

// Conditions
Value* buildCond(CodeGenCtx& CG, CmpOp op, const string& a, const string& b) {
    Value* va = buildExprString(CG, a, true);
    Value* vb = buildExprString(CG, b, true);
    switch (op) {
    case LT:
        return CG.Builder.CreateICmpSLT(va, vb, "cmplt");
    case GT:
        return CG.Builder.CreateICmpSGT(va, vb, "cmpgt");
    case LE:
        return CG.Builder.CreateICmpSLE(va, vb, "cmple");
    case GE:
        return CG.Builder.CreateICmpSGE(va, vb, "cmpge");
    case EQ:
        return CG.Builder.CreateICmpEQ(va, vb, "cmpeq");
    case NE:
        return CG.Builder.CreateICmpNE(va, vb, "cmpne");
    }
    return nullptr;
}

// Statement codegen
void codegenBlock(CodeGenCtx& CG, const vector<Stmt>& blk);

void codegenStmt(CodeGenCtx& CG, const Stmt& s) {
    IRBuilder<>& B = CG.Builder;
    LLVMContext& Ctx = CG.Ctx;

    switch (s.type) {
    case Stmt::YOSORO: { // print
        Value* v = buildExprString(CG, s.expr, true);
        CG.emitPrintI64(v);
        break;
    }
    case Stmt::SET: { // assign
        Value* rhs = buildExprString(CG, s.rhsExpr, true);
        if (s.lhsIsArray) {
            Value* idx = buildExprString(CG, s.lhsIndexExpr, false);
            CG.storeArrayElem(s.lhsName, idx, rhs);
        } else {
            CG.storeScalar(s.lhsName, rhs);
        }
        break;
    }
    case Stmt::IHU: { // if
        Function* F = CG.MainFn;
        Value* cond = buildCond(CG, s.op, s.condA, s.condB);

        BasicBlock* ThenBB = BasicBlock::Create(Ctx, "if.then", F);
        BasicBlock* MergeBB = BasicBlock::Create(Ctx, "if.end", F);

        B.CreateCondBr(cond, ThenBB, MergeBB);

        B.SetInsertPoint(ThenBB);
        codegenBlock(CG, s.body);
        if (!ThenBB->getTerminator())
            B.CreateBr(MergeBB);

        B.SetInsertPoint(MergeBB);
        break;
    }
    case Stmt::WHILE_: { // while
        Function* F = CG.MainFn;
        BasicBlock* CondBB = BasicBlock::Create(Ctx, "while.cond", F);
        BasicBlock* BodyBB = BasicBlock::Create(Ctx, "while.body", F);
        BasicBlock* AfterBB = BasicBlock::Create(Ctx, "while.end", F);

        B.CreateBr(CondBB);

        B.SetInsertPoint(CondBB);
        {
            Value* c = buildCond(CG, s.op, s.condA, s.condB);
            B.CreateCondBr(c, BodyBB, AfterBB);
        }

        B.SetInsertPoint(BodyBB);
        codegenBlock(CG, s.body);
        if (!BodyBB->getTerminator())
            B.CreateBr(CondBB);

        B.SetInsertPoint(AfterBB);
        break;
    }
    case Stmt::HOR: { // for
        Function* F = CG.MainFn;
        Value* startVal = buildExprString(CG, s.forStart, true);
        Value* endVal = buildExprString(CG, s.forEnd, true);

        if (s.forVarIsArray) {
            Value* idx = buildExprString(CG, s.forVarIndexExpr, false);
            CG.storeArrayElem(s.forVarName, idx, startVal);
        } else {
            CG.storeScalar(s.forVarName, startVal);
        }

        BasicBlock* CondBB = BasicBlock::Create(Ctx, "for.cond", F);
        BasicBlock* BodyBB = BasicBlock::Create(Ctx, "for.body", F);
        BasicBlock* StepBB = BasicBlock::Create(Ctx, "for.inc", F);
        BasicBlock* AfterBB = BasicBlock::Create(Ctx, "for.end", F);

        B.CreateBr(CondBB);

        B.SetInsertPoint(CondBB);
        {
            Value* iVal;
            if (s.forVarIsArray) {
                Value* idx = buildExprString(CG, s.forVarIndexExpr, false);
                iVal = CG.loadArrayElem(s.forVarName, idx);
            } else {
                iVal = CG.loadScalar(s.forVarName);
            }
            Value* c = B.CreateICmpSLE(iVal, endVal, "forcond");
            B.CreateCondBr(c, BodyBB, AfterBB);
        }

        B.SetInsertPoint(BodyBB);
        codegenBlock(CG, s.body);
        if (!BodyBB->getTerminator())
            B.CreateBr(StepBB);

        B.SetInsertPoint(StepBB);
        {
            Value* iVal;
            if (s.forVarIsArray) {
                Value* idx = buildExprString(CG, s.forVarIndexExpr, false);
                iVal = CG.loadArrayElem(s.forVarName, idx);
            } else {
                iVal = CG.loadScalar(s.forVarName);
            }
            Value* nxt = B.CreateAdd(iVal, CG.C1_64, "inc"); // increment
            if (s.forVarIsArray) {
                Value* idx = buildExprString(CG, s.forVarIndexExpr, false);
                CG.storeArrayElem(s.forVarName, idx, nxt);
            } else {
                CG.storeScalar(s.forVarName, nxt);
            }
            B.CreateBr(CondBB);
        }

        B.SetInsertPoint(AfterBB);

        // If the loop was supposed to run, set the variable to its end value.
        Value* loopDidRunCond = B.CreateICmpSLE(startVal, endVal, "loopDidRun");
        BasicBlock* SetFinalVarBB = BasicBlock::Create(Ctx, "for.setfinal", F);
        BasicBlock* FinalMergeBB = BasicBlock::Create(Ctx, "for.finalmerge", F);
        B.CreateCondBr(loopDidRunCond, SetFinalVarBB, FinalMergeBB);

        B.SetInsertPoint(SetFinalVarBB);
        if (s.forVarIsArray) {
            Value* idx = buildExprString(CG, s.forVarIndexExpr, false);
            CG.storeArrayElem(s.forVarName, idx, endVal);
        } else {
            CG.storeScalar(s.forVarName, endVal);
        }
        B.CreateBr(FinalMergeBB);

        B.SetInsertPoint(FinalMergeBB);
        break;
    }
    }
}

void codegenBlock(CodeGenCtx& CG, const vector<Stmt>& blk) {
    for (const auto& st : blk) {
        codegenStmt(CG, st);
    }
}

// Main
int main(int argc, char** argv) {
    if (argc != 3) {
        errs() << std::format("Usage: {} <input.cyaron> <output.ll>\n",
                              argv[0]);
        return 1;
    }
    string inputFile = argv[1];
    string outputFile = argv[2];

    ifstream ifs(inputFile);
    if (!ifs) {
        errs() << std::format("Error: cannot open input file {}\n", inputFile);
        return 1;
    }

    string line;
    while (getline(ifs, line)) {
        size_t comment_pos = line.find('#');
        if (comment_pos != string::npos) {
            line = line.substr(0, comment_pos);
        }
        gLines.push_back(line);
    }

    gPosLine = 0;
    size_t tmpPos = 0;
    vector<VarDecl> decls = parse_vars_block(gLines, tmpPos);
    gPosLine = tmpPos;

    vector<Stmt> program = parse_program_rest();

    CodeGenCtx CG("CYaRonModule");

    for (const auto& vd : decls) {
        CG.declareVar(vd);
    }

    codegenBlock(CG, program);

    CG.emitNewline();
    CG.Builder.CreateRet(ConstantInt::get(CG.I32, 0));

    if (verifyFunction(*CG.MainFn, &errs())) {
        errs() << "Function verification failed.\n";
        return 1;
    }
    if (verifyModule(*CG.Mod, &errs())) {
        errs() << "Module verification failed.\n";
        return 1;
    }

    std::error_code EC;
    raw_fd_ostream dest(outputFile, EC, sys::fs::OF_None);

    if (EC) {
        errs() << std::format("Could not open file: {}", EC.message());
        return 1;
    }

    CG.Mod->print(dest, nullptr);
    dest.flush();
    return 0;
}