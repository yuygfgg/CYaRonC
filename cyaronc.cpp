#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <utility>
#include <vector>

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

// Constants
static constexpr std::string_view IHU_PREFIX = "ihu";
static constexpr std::string_view HOR_PREFIX = "hor";
static constexpr std::string_view WHILE_PREFIX = "while";
static constexpr std::string_view VARS_PREFIX = "vars";
static constexpr std::string_view SET_PREFIX = ":set";
static constexpr std::string_view YOSORO_PREFIX = ":yosoro";
static constexpr std::string_view INPUT_PREFIX = ":input";
// AST Node Definitions
enum class CmpOp { LT, GT, LE, GE, EQ, NE };
enum class VarType { INT, FLOAT };

struct Stmt {
    enum class Type { YOSORO, SET, IHU, HOR, WHILE_, INPUT };
    Type type;
    std::size_t line_number;

    // YOSORO (print)
    std::string expr;

    // SET (assignment) / INPUT
    std::string lhsName;
    bool lhsIsArray = false;
    std::string lhsIndexExpr;
    std::string rhsExpr;

    // IHU (if) / WHILE
    CmpOp op;
    std::string condA, condB;
    std::vector<Stmt> body;

    // HOR (for)
    std::string forVarName;
    bool forVarIsArray = false;
    std::string forVarIndexExpr;
    std::string forStart, forEnd;
};

struct VarDecl {
    std::string name;
    VarType type = VarType::INT;
    bool isArray = false;
    int64_t L = 0, R = -1;
};

struct Program {
    std::vector<VarDecl> varDecls;
    std::vector<Stmt> stmts;
};

// Utility Functions
namespace StringUtils {
static inline std::string rtrim_cr(std::string s) {
    if (!s.empty() && (s.back() == '\r' || s.back() == '\n')) {
        while (!s.empty() && (s.back() == '\r' || s.back() == '\n'))
            s.pop_back();
    }
    return s;
}

static inline std::string trim(const std::string& s) {
    std::size_t i = 0, j = s.size();
    while (i < j && std::isspace(static_cast<unsigned char>(s[i])))
        ++i;
    while (j > i && std::isspace(static_cast<unsigned char>(s[j - 1])))
        --j;
    return s.substr(i, j - i);
}

static inline bool starts_with(const std::string& s, std::string_view p) {
    return s.size() >= p.size() && s.compare(0, p.size(), p) == 0;
}

static inline std::string remove_spaces(const std::string& s) {
    std::string t;
    t.reserve(s.size());
    for (unsigned char c : s)
        if (!std::isspace(static_cast<unsigned char>(c)))
            t.push_back(c);
    return t;
}

static inline bool is_valid_identifier(const std::string& s) {
    if (s.empty()) {
        return false;
    }
    if (!std::isalpha(static_cast<unsigned char>(s[0])) && s[0] != '_') {
        return false;
    }
    for (size_t i = 1; i < s.size(); ++i) {
        if (!std::isalnum(static_cast<unsigned char>(s[i])) && s[i] != '_') {
            return false;
        }
    }
    return true;
}

static inline std::vector<std::string>
split_by_commas_no_space(const std::string& s) {
    std::vector<std::string> parts;
    std::size_t i = 0, n = s.size();
    std::size_t last = 0;
    while (i <= n) {
        if (i == n || s[i] == ',') {
            parts.push_back(s.substr(last, i - last));
            last = i + 1;
        }
        ++i;
    }
    return parts;
}
} // namespace StringUtils

// Error Reporting
[[noreturn]] void reportError(const std::string& message,
                              std::size_t line_number,
                              llvm::raw_ostream* OS = &llvm::errs()) {
    *OS << std::format("Error on line {}: {}\n", line_number, message);
    std::exit(1);
}

// Parser
class Parser {
  public:
    explicit Parser(std::vector<std::string> lines)
        : lines_(std::move(lines)), pos_(0) {}

    Program parse_program() {
        Program prog;
        prog.varDecls = parse_vars_block_if_present();
        prog.stmts = parse_body(true);
        return prog;
    }

  private:
    std::vector<std::string> lines_;
    std::size_t pos_;

    struct VarRef {
        std::string name;
        bool isArray = false;
        std::string indexExpr;
    };

    // Parsing Primitives
    bool eof() const { return pos_ >= lines_.size(); }
    std::size_t current_line_num() const { return pos_ + 1; }
    const std::string& current_line() { return lines_[pos_]; }
    void advance() { ++pos_; }

    CmpOp parse_op(const std::string& s) {
        if (s == "lt")
            return CmpOp::LT;
        if (s == "gt")
            return CmpOp::GT;
        if (s == "le")
            return CmpOp::LE;
        if (s == "ge")
            return CmpOp::GE;
        if (s == "eq")
            return CmpOp::EQ;
        if (s == "neq")
            return CmpOp::NE;
        reportError(std::format("Invalid comparison operator '{}'", s),
                    current_line_num());
    }

    VarRef parse_var_ref(const std::string& s) {
        VarRef ref;
        std::size_t lb = s.find('[');
        if (lb == std::string::npos) {
            ref.name = s;
            ref.isArray = false;
        } else {
            ref.name = s.substr(0, lb);
            std::size_t rb = s.rfind(']');
            if (rb == std::string::npos || rb <= lb)
                reportError("Mismatched brackets in variable access.",
                            current_line_num());
            ref.isArray = true;
            ref.indexExpr = s.substr(lb + 1, rb - lb - 1);
            if (ref.indexExpr.empty())
                reportError("Empty index in array access.", current_line_num());
        }
        return ref;
    }

    int64_t parse_int_literal(const std::string& str) {
        if (str.empty())
            reportError("Empty number in array range.", current_line_num());
        int32_t sign = 1;
        std::size_t i = 0;
        if (str[0] == '+') {
            i = 1;
        } else if (str[0] == '-') {
            sign = -1;
            i = 1;
        }
        if (i == str.size())
            reportError(std::format("Invalid number in array range: {}\n", str),
                        current_line_num());
        int64_t v = 0;
        for (; i < str.size(); ++i) {
            if (!std::isdigit(static_cast<unsigned char>(str[i])))
                reportError(
                    std::format("Invalid number in array range: {}\n", str),
                    current_line_num());
            v = v * 10 + (str[i] - '0');
        }
        return sign * v;
    }

    // Statement Parsers
    std::vector<Stmt> parse_body(bool is_top_level) {
        std::vector<Stmt> body;
        while (!eof()) {
            std::string t =
                StringUtils::trim(StringUtils::rtrim_cr(current_line()));

            if (t.empty()) {
                advance();
                continue;
            }
            if (t == "}") {
                if (is_top_level) {
                    reportError("Unexpected '}' at top level.",
                                current_line_num());
                }
                advance();
                break;
            }

            if (t[0] == '{') {
                body.push_back(parse_block_stmt());
            } else {
                body.push_back(parse_simple_stmt());
            }
        }
        return body;
    }

    Stmt parse_simple_stmt() {
        std::size_t line_num = current_line_num();
        std::string t =
            StringUtils::trim(StringUtils::rtrim_cr(current_line()));
        advance();

        Stmt s{};
        s.line_number = line_num;

        if (StringUtils::starts_with(t, SET_PREFIX)) {
            std::string rest = StringUtils::trim(t.substr(SET_PREFIX.size()));
            std::string rs = StringUtils::remove_spaces(rest);
            auto parts = StringUtils::split_by_commas_no_space(rs);
            if (parts.size() != 2)
                reportError(
                    "Invalid ':set' statement. Expected ':set <lhs>, <rhs>'.",
                    line_num);

            if (parts[0].empty())
                reportError("Missing left-hand side in ':set' statement.",
                            line_num);
            if (parts[1].empty())
                reportError("Missing right-hand side in ':set' statement.",
                            line_num);

            s.type = Stmt::Type::SET;
            VarRef lhs = parse_var_ref(parts[0]);
            s.lhsName = lhs.name;
            s.lhsIsArray = lhs.isArray;
            s.lhsIndexExpr = lhs.indexExpr;
            s.rhsExpr = parts[1];

        } else if (StringUtils::starts_with(t, YOSORO_PREFIX)) {
            s.type = Stmt::Type::YOSORO;
            s.expr = StringUtils::trim(t.substr(YOSORO_PREFIX.size()));
        } else if (StringUtils::starts_with(t, INPUT_PREFIX)) {
            std::string rest = StringUtils::trim(t.substr(INPUT_PREFIX.size()));
            if (rest.empty())
                reportError("Missing variable for ':input' statement.",
                            line_num);
            s.type = Stmt::Type::INPUT;
            VarRef lhs = parse_var_ref(rest);
            s.lhsName = lhs.name;
            s.lhsIsArray = lhs.isArray;
            s.lhsIndexExpr = lhs.indexExpr;
        } else {
            reportError(std::format("Unknown statement: {}\n", t), line_num);
        }
        return s;
    }

    Stmt parse_block_stmt() {
        std::size_t line_num = current_line_num();
        std::string t =
            StringUtils::trim(StringUtils::rtrim_cr(current_line()));
        std::string hdr = StringUtils::trim(t.substr(1));
        advance(); // Consume opening brace line

        Stmt s{};
        s.line_number = line_num;

        if (StringUtils::starts_with(hdr, IHU_PREFIX)) {
            std::string rest = StringUtils::trim(hdr.substr(IHU_PREFIX.size()));
            auto parts = StringUtils::split_by_commas_no_space(
                StringUtils::remove_spaces(rest));
            if (parts.size() != 3)
                reportError("Invalid 'ihu' statement. Expected '{ihu <op>, "
                            "<expr1>, <expr2>}'.",
                            line_num);
            s.type = Stmt::Type::IHU;
            s.op = parse_op(parts[0]);
            s.condA = parts[1];
            s.condB = parts[2];
            s.body = parse_body(false);
        } else if (StringUtils::starts_with(hdr, HOR_PREFIX)) {
            std::string rest = StringUtils::trim(hdr.substr(HOR_PREFIX.size()));
            auto parts = StringUtils::split_by_commas_no_space(
                StringUtils::remove_spaces(rest));
            if (parts.size() != 3)
                reportError("Invalid 'hor' statement. Expected '{hor <var>, "
                            "<start>, <end>}'.",
                            line_num);
            s.type = Stmt::Type::HOR;
            VarRef v = parse_var_ref(parts[0]);
            s.forVarName = v.name;
            s.forVarIsArray = v.isArray;
            s.forVarIndexExpr = v.indexExpr;
            s.forStart = parts[1];
            s.forEnd = parts[2];
            s.body = parse_body(false);
        } else if (StringUtils::starts_with(hdr, WHILE_PREFIX)) {
            std::string rest =
                StringUtils::trim(hdr.substr(WHILE_PREFIX.size()));
            auto parts = StringUtils::split_by_commas_no_space(
                StringUtils::remove_spaces(rest));
            if (parts.size() != 3)
                reportError("Invalid 'while' statement. Expected '{while <op>, "
                            "<expr1>, <expr2>}'.",
                            line_num);
            s.type = Stmt::Type::WHILE_;
            s.op = parse_op(parts[0]);
            s.condA = parts[1];
            s.condB = parts[2];
            s.body = parse_body(false);
        } else if (StringUtils::starts_with(hdr, VARS_PREFIX)) {
            reportError("Duplicate 'vars' block is not allowed.", line_num);
        } else {
            reportError(
                std::format("Unknown block type starting with '{}'\n", hdr),
                line_num);
        }
        return s;
    }

    std::vector<VarDecl> parse_vars_block_if_present() {
        while (!eof() && StringUtils::trim(current_line()).empty()) {
            advance();
        }
        if (eof())
            return {};

        std::string t =
            StringUtils::trim(StringUtils::rtrim_cr(current_line()));
        if (t.empty() || t[0] != '{')
            return {};

        std::string hdr = StringUtils::trim(t.substr(1));
        if (!StringUtils::starts_with(hdr, VARS_PREFIX)) {
            if (StringUtils::starts_with(hdr, "ihu") ||
                StringUtils::starts_with(hdr, "hor") ||
                StringUtils::starts_with(hdr, "while")) {
                // It's a regular block, not a vars block.
                return {};
            }
            reportError("Duplicate 'vars' block is not allowed, or invalid "
                        "block at top level.",
                        current_line_num());
        }

        advance(); // Consume '{vars' line

        std::vector<VarDecl> decls;
        while (!eof()) {
            std::size_t var_line_num = current_line_num();
            std::string s =
                StringUtils::trim(StringUtils::rtrim_cr(current_line()));
            advance();

            if (s == "}")
                break;
            if (s.empty())
                continue;

            std::size_t colon = s.find(':');
            if (colon == std::string::npos)
                reportError(
                    "Invalid variable declaration. Expected '<name>:<type>'.",
                    var_line_num);

            VarDecl vd;
            vd.name = StringUtils::trim(s.substr(0, colon));
            if (!StringUtils::is_valid_identifier(vd.name)) {
                reportError(std::format("Invalid identifier '{}'", vd.name),
                            var_line_num);
            }
            std::string kind = StringUtils::trim(s.substr(colon + 1));

            if (kind == "int") {
                vd.isArray = false;
                vd.type = VarType::INT;
            } else if (kind == "float") {
                vd.isArray = false;
                vd.type = VarType::FLOAT;
            } else if (StringUtils::starts_with(kind, "array[") &&
                       kind.back() == ']') {
                std::string inside =
                    kind.substr(sizeof("array[") - 1,
                                kind.size() - (sizeof("array[") - 1) - 1);

                auto comma_pos = inside.find(',');
                if (comma_pos == std::string::npos)
                    reportError("Invalid array declaration. Expected "
                                "'array[type,L..R]'.",
                                var_line_num);

                std::string type_str =
                    StringUtils::trim(inside.substr(0, comma_pos));
                if (type_str == "int") {
                    vd.type = VarType::INT;
                } else if (type_str == "float") {
                    vd.type = VarType::FLOAT;
                } else {
                    reportError(std::format("Invalid array element type '{}'.",
                                            type_str),
                                var_line_num);
                }

                std::string range_str =
                    StringUtils::trim(inside.substr(comma_pos + 1));
                std::size_t dots = range_str.find("..");
                if (dots == std::string::npos)
                    reportError("Invalid array range. Expected 'L..R'.",
                                var_line_num);

                vd.isArray = true;
                std::string lstr = StringUtils::trim(range_str.substr(0, dots));
                std::string rstr =
                    StringUtils::trim(range_str.substr(dots + 2));

                if (lstr.empty() || rstr.empty())
                    reportError("Invalid array range. Expected 'L..R'.",
                                var_line_num);

                vd.L = parse_int_literal(lstr);
                vd.R = parse_int_literal(rstr);
            } else {
                reportError(
                    std::format("Invalid type '{}'. Expected 'int', 'float', "
                                "or 'array[type,L..R]'.\n",
                                kind),
                    var_line_num);
            }
            decls.push_back(std::move(vd));
        }
        return decls;
    }
};

// Code Generator
class CodeGenerator {
  private:
    struct TypedValue {
        llvm::Value* val = nullptr;
        VarType type = VarType::INT;
    };

    struct Sym {
        VarType type;
        bool isArray = false;
        llvm::AllocaInst* allocaInst = nullptr;
        int64_t L = 0, R = -1;
        llvm::ArrayType* arrTy = nullptr;
    };

    llvm::LLVMContext Ctx;
    std::unique_ptr<llvm::Module> Mod;
    llvm::IRBuilder<> Builder;
    llvm::IRBuilder<> AllocaBuilder;
    llvm::Function* MainFn = nullptr;

    llvm::FunctionCallee Printf;
    llvm::FunctionCallee Putchar;
    llvm::FunctionCallee Scanf;

    std::unordered_map<std::string, Sym> SymbolTable;

    llvm::Type* F64;
    llvm::Type* I64;
    llvm::Type* I32;
    llvm::Type* I8;
    llvm::Value* C0_64;
    llvm::Value* C1_64;
    llvm::Value* C10_32;

  public:
    explicit CodeGenerator(const std::string& moduleName)
        : Mod(std::make_unique<llvm::Module>(moduleName, Ctx)), Builder(Ctx),
          AllocaBuilder(Ctx) {
        F64 = llvm::Type::getDoubleTy(Ctx);
        I64 = llvm::Type::getInt64Ty(Ctx);
        I32 = llvm::Type::getInt32Ty(Ctx);
        I8 = llvm::Type::getInt8Ty(Ctx);
        C0_64 = llvm::ConstantInt::get(I64, 0);
        C1_64 = llvm::ConstantInt::get(I64, 1);
        C10_32 = llvm::ConstantInt::get(I32, 10); // '\n'

        llvm::FunctionType* FT = llvm::FunctionType::get(I32, false);
        MainFn = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,
                                        "main", Mod.get());
        llvm::BasicBlock* EntryBB =
            llvm::BasicBlock::Create(Ctx, "entry", MainFn);
        Builder.SetInsertPoint(EntryBB);
        AllocaBuilder.SetInsertPoint(EntryBB, EntryBB->begin());

        Printf = Mod->getOrInsertFunction(
            "printf",
            llvm::FunctionType::get(I32, llvm::PointerType::get(Ctx, 0), true));
        Putchar = Mod->getOrInsertFunction(
            "putchar", llvm::FunctionType::get(I32, I32, false));
        Scanf = Mod->getOrInsertFunction(
            "scanf",
            llvm::FunctionType::get(I32, llvm::PointerType::get(Ctx, 0), true));
    }

    void generate(const Program& prog) {
        for (const auto& vd : prog.varDecls) {
            declareVar(vd);
        }

        codegenBlock(prog.stmts);

        emitNewline();
        Builder.CreateRet(llvm::ConstantInt::get(I32, 0));

        if (llvm::verifyFunction(*MainFn, &llvm::errs())) {
            llvm::errs() << "Function verification failed.\n";
            std::exit(1);
        }
        if (llvm::verifyModule(*Mod, &llvm::errs())) {
            llvm::errs() << "Module verification failed.\n";
            std::exit(1);
        }
    }

    void writeToFile(const std::string& outputFile) {
        std::error_code EC;
        llvm::raw_fd_ostream dest(outputFile, EC, llvm::sys::fs::OF_None);
        if (EC) {
            llvm::errs() << std::format("Could not open file: {}\\n",
                                        EC.message());
            std::exit(1);
        }
        Mod->print(dest, nullptr);
        dest.flush();
    }

  private:
    void emitNewline() { Builder.CreateCall(Putchar, {C10_32}); }

    void declareVar(const VarDecl& vd) {
        llvm::Type* llvmType = (vd.type == VarType::FLOAT) ? F64 : I64;
        if (!vd.isArray) {
            llvm::AllocaInst* A =
                AllocaBuilder.CreateAlloca(llvmType, nullptr, vd.name);
            if (vd.type == VarType::INT) {
                Builder.CreateStore(C0_64, A);
            } else {
                Builder.CreateStore(llvm::ConstantFP::get(F64, 0.0), A);
            }
            SymbolTable[vd.name] = {vd.type, false, A, 0, -1, nullptr};
        } else {
            int64_t N = (vd.R >= vd.L) ? (vd.R - vd.L + 1) : 0;
            if (N <= 0)
                N = 1;
            llvm::ArrayType* AT = llvm::ArrayType::get(llvmType, (uint64_t)N);
            llvm::AllocaInst* A =
                AllocaBuilder.CreateAlloca(AT, nullptr, vd.name);
            Builder.CreateStore(llvm::ConstantAggregateZero::get(AT), A);
            SymbolTable[vd.name] = {vd.type, true, A, vd.L, vd.R, AT};
        }
    }

    llvm::Value* getArrayElemPtr(const std::string& name, llvm::Value* idxVal) {
        auto it = SymbolTable.find(name);
        assert(it != SymbolTable.end() && it->second.isArray);
        Sym& s = it->second;
        llvm::Value* rel = Builder.CreateSub(
            idxVal, llvm::ConstantInt::get(I64, s.L), name + ".relidx");
        llvm::Type* elemType = (s.type == VarType::FLOAT) ? F64 : I64;
        llvm::Value* ptr0 = Builder.CreateInBoundsGEP(
            s.arrTy, s.allocaInst, {C0_64, C0_64}, name + ".ptr0");
        return Builder.CreateInBoundsGEP(elemType, ptr0, rel,
                                         name + ".elemptr");
    }

    void storeScalar(const std::string& name, llvm::Value* v) {
        auto it = SymbolTable.find(name);
        assert(it != SymbolTable.end() && !it->second.isArray);
        Builder.CreateStore(v, it->second.allocaInst);
    }

    void storeArrayElem(const std::string& name, llvm::Value* idxVal,
                        llvm::Value* v) {
        Builder.CreateStore(v, getArrayElemPtr(name, idxVal));
    }

    TypedValue buildExpr(const std::string& s, bool allowArray,
                         std::size_t line_number);
    TypedValue buildExprCore(const std::string& t, bool allowArray,
                             std::size_t line_number);
    llvm::Value* buildCond(CmpOp op, const std::string& a, const std::string& b,
                           std::size_t line_number);
    void codegenBlock(const std::vector<Stmt>& blk);
    void codegenStmt(const Stmt& s);
};

CodeGenerator::TypedValue CodeGenerator::buildExpr(const std::string& s,
                                                   bool allowArray,
                                                   std::size_t line_number) {
    return buildExprCore(StringUtils::remove_spaces(s), allowArray,
                         line_number);
}

CodeGenerator::TypedValue
CodeGenerator::buildExprCore(const std::string& t, bool allowArray,
                             std::size_t line_number) {
    std::size_t i = 0, n = t.size();
    TypedValue res;
    int32_t sign = +1;

    auto applySignAndAcc = [&](TypedValue term) {
        if (sign == -1) {
            if (term.type == VarType::INT) {
                term.val = Builder.CreateSub(C0_64, term.val, "negtmp");
            } else {
                term.val = Builder.CreateFSub(llvm::ConstantFP::get(F64, 0.0),
                                              term.val, "fnegtmp");
            }
        }

        if (!res.val) {
            res = term;
        } else {
            TypedValue lhs = res;
            TypedValue rhs = term;
            if (lhs.type == VarType::FLOAT && rhs.type == VarType::INT) {
                rhs.val = Builder.CreateSIToFP(rhs.val, F64, "cast");
                rhs.type = VarType::FLOAT;
            } else if (lhs.type == VarType::INT && rhs.type == VarType::FLOAT) {
                lhs.val = Builder.CreateSIToFP(lhs.val, F64, "cast");
                lhs.type = VarType::FLOAT;
            }

            if (lhs.type == VarType::INT) { // both are ints
                assert(rhs.type == VarType::INT);
                res.val = Builder.CreateAdd(lhs.val, rhs.val, "addtmp");
                res.type = VarType::INT;
            } else { // both are floats
                assert(rhs.type == VarType::FLOAT);
                res.val = Builder.CreateFAdd(lhs.val, rhs.val, "faddtmp");
                res.type = VarType::FLOAT;
            }
        }
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

        if (std::isdigit(static_cast<unsigned char>(t[i]))) {
            std::size_t start_i = i;
            bool is_float = false;
            while (i < n && std::isdigit(static_cast<unsigned char>(t[i])))
                i++;
            if (i < n && t[i] == '.') {
                is_float = true;
                i++;
                while (i < n && std::isdigit(static_cast<unsigned char>(t[i])))
                    i++;
            }
            std::string num_str = t.substr(start_i, i - start_i);
            if (is_float) {
                double v = std::stod(num_str);
                applySignAndAcc(
                    {llvm::ConstantFP::get(F64, v), VarType::FLOAT});
            } else {
                int64_t v = std::stoll(num_str);
                applySignAndAcc({llvm::ConstantInt::get(I64, v), VarType::INT});
            }
        } else if (std::isalpha(static_cast<unsigned char>(t[i])) ||
                   t[i] == '_') {
            std::string name;
            name.push_back(t[i++]);
            while (i < n && (std::isalnum(static_cast<unsigned char>(t[i])) ||
                             t[i] == '_'))
                name.push_back(t[i++]);

            auto it = SymbolTable.find(name);
            if (it == SymbolTable.end()) {
                reportError(std::format("Unknown variable '{}'", name),
                            line_number);
            }

            if (i < n && t[i] == '[') {
                if (!allowArray) {
                    reportError("Unexpected array access in this expression.",
                                line_number);
                }
                std::size_t start = i + 1, j = start, d = 1;
                while (j < n && d > 0) {
                    if (t[j] == '[')
                        d++;
                    else if (t[j] == ']')
                        d--;
                    j++;
                }
                TypedValue idx_tv = buildExpr(t.substr(start, j - 1 - start),
                                              false, line_number);
                if (idx_tv.type == VarType::FLOAT) {
                    reportError("Array index cannot be a float.", line_number);
                }
                i = j;

                llvm::Value* ptr = getArrayElemPtr(name, idx_tv.val);
                llvm::Type* elemType =
                    (it->second.type == VarType::FLOAT) ? F64 : I64;
                applySignAndAcc(
                    {Builder.CreateLoad(elemType, ptr, name + ".elem"),
                     it->second.type});
            } else {
                llvm::Type* elemType =
                    (it->second.type == VarType::FLOAT) ? F64 : I64;
                applySignAndAcc(
                    {Builder.CreateLoad(elemType, it->second.allocaInst,
                                        name + ".val"),
                     it->second.type});
            }
        } else {
            reportError(std::format("Unknown token '{}' in expression",
                                    std::string(1, t[i])),
                        line_number);
        }
    }
    if (!res.val) {
        return {C0_64, VarType::INT};
    }
    return res;
}

llvm::Value* CodeGenerator::buildCond(CmpOp op, const std::string& a,
                                      const std::string& b,
                                      std::size_t line_number) {
    TypedValue va_tv = buildExpr(a, true, line_number);
    TypedValue vb_tv = buildExpr(b, true, line_number);

    if (va_tv.type == VarType::FLOAT && vb_tv.type == VarType::INT) {
        vb_tv.val = Builder.CreateSIToFP(vb_tv.val, F64, "cast.cond");
        vb_tv.type = VarType::FLOAT;
    } else if (va_tv.type == VarType::INT && vb_tv.type == VarType::FLOAT) {
        va_tv.val = Builder.CreateSIToFP(va_tv.val, F64, "cast.cond");
        va_tv.type = VarType::FLOAT;
    }

    if (va_tv.type == VarType::INT) {
        assert(vb_tv.type == VarType::INT);
        switch (op) {
        case CmpOp::LT:
            return Builder.CreateICmpSLT(va_tv.val, vb_tv.val, "cmplt");
        case CmpOp::GT:
            return Builder.CreateICmpSGT(va_tv.val, vb_tv.val, "cmpgt");
        case CmpOp::LE:
            return Builder.CreateICmpSLE(va_tv.val, vb_tv.val, "cmple");
        case CmpOp::GE:
            return Builder.CreateICmpSGE(va_tv.val, vb_tv.val, "cmpge");
        case CmpOp::EQ:
            return Builder.CreateICmpEQ(va_tv.val, vb_tv.val, "cmpeq");
        case CmpOp::NE:
            return Builder.CreateICmpNE(va_tv.val, vb_tv.val, "cmpne");
        }
    } else {
        assert(vb_tv.type == VarType::FLOAT);
        llvm::CmpInst::Predicate p;
        switch (op) {
        case CmpOp::LT:
            p = llvm::CmpInst::FCMP_OLT;
            break;
        case CmpOp::GT:
            p = llvm::CmpInst::FCMP_OGT;
            break;
        case CmpOp::LE:
            p = llvm::CmpInst::FCMP_OLE;
            break;
        case CmpOp::GE:
            p = llvm::CmpInst::FCMP_OGE;
            break;
        case CmpOp::EQ:
            p = llvm::CmpInst::FCMP_OEQ;
            break;
        case CmpOp::NE:
            p = llvm::CmpInst::FCMP_ONE;
            break;
        }
        return Builder.CreateFCmp(p, va_tv.val, vb_tv.val, "fcmp");
    }
    return nullptr;
}

void CodeGenerator::codegenBlock(const std::vector<Stmt>& blk) {
    for (const auto& st : blk) {
        codegenStmt(st);
    }
}

void CodeGenerator::codegenStmt(const Stmt& s) {
    switch (s.type) {
    case Stmt::Type::YOSORO: {
        TypedValue tv = buildExpr(s.expr, true, s.line_number);
        const char* fmt_str = (tv.type == VarType::INT) ? "%lld " : "%f ";
        auto* gv = Builder.CreateGlobalString(fmt_str, "fmt");
        llvm::Value* idx0 = llvm::ConstantInt::get(I64, 0);
        llvm::Value* fmtPtr = Builder.CreateInBoundsGEP(
            gv->getValueType(), gv, llvm::ArrayRef<llvm::Value*>{idx0, idx0},
            "fmt.ptr");
        Builder.CreateCall(Printf, {fmtPtr, tv.val});
        break;
    }
    case Stmt::Type::SET: {
        TypedValue rhs = buildExpr(s.rhsExpr, true, s.line_number);

        auto it = SymbolTable.find(s.lhsName);
        if (it == SymbolTable.end()) {
            reportError(
                std::format("Undeclared variable '{}' in set", s.lhsName),
                s.line_number);
        }
        VarType lhsType = it->second.type;

        llvm::Value* valToStore = rhs.val;
        if (lhsType == VarType::FLOAT && rhs.type == VarType::INT) {
            valToStore = Builder.CreateSIToFP(valToStore, F64, "cast");
        } else if (lhsType == VarType::INT && rhs.type == VarType::FLOAT) {
            valToStore = Builder.CreateFPToSI(valToStore, I64, "cast");
        }

        if (s.lhsIsArray) {
            TypedValue idx_tv = buildExpr(s.lhsIndexExpr, false, s.line_number);
            if (idx_tv.type == VarType::FLOAT) {
                reportError("Array index cannot be a float.", s.line_number);
            }
            storeArrayElem(s.lhsName, idx_tv.val, valToStore);
        } else {
            storeScalar(s.lhsName, valToStore);
        }
        break;
    }
    case Stmt::Type::INPUT: {
        llvm::Value* ptr;
        auto it = SymbolTable.find(s.lhsName);
        if (it == SymbolTable.end()) {
            reportError(
                std::format("Undeclared variable '{}' in input", s.lhsName),
                s.line_number);
        }
        VarType type = it->second.type;

        if (s.lhsIsArray) {
            TypedValue idx_tv = buildExpr(s.lhsIndexExpr, false, s.line_number);
            if (idx_tv.type == VarType::FLOAT) {
                reportError("Array index cannot be a float.", s.line_number);
            }
            ptr = getArrayElemPtr(s.lhsName, idx_tv.val);
        } else {
            ptr = it->second.allocaInst;
        }

        const char* fmt_str = (type == VarType::INT) ? "%lld" : "%lf";
        auto* gv = Builder.CreateGlobalString(fmt_str, "scanf_fmt");
        llvm::Value* fmtPtr = Builder.CreateInBoundsGEP(
            gv->getValueType(), gv, {C0_64, C0_64}, "fmt.ptr");

        Builder.CreateCall(Scanf, {fmtPtr, ptr});
        break;
    }
    case Stmt::Type::IHU: {
        llvm::Value* cond = buildCond(s.op, s.condA, s.condB, s.line_number);
        llvm::BasicBlock* ThenBB =
            llvm::BasicBlock::Create(Ctx, "if.then", MainFn);
        llvm::BasicBlock* MergeBB =
            llvm::BasicBlock::Create(Ctx, "if.end", MainFn);
        Builder.CreateCondBr(cond, ThenBB, MergeBB);
        Builder.SetInsertPoint(ThenBB);
        codegenBlock(s.body);
        if (!Builder.GetInsertBlock()->getTerminator())
            Builder.CreateBr(MergeBB);
        Builder.SetInsertPoint(MergeBB);
        break;
    }
    case Stmt::Type::WHILE_: {
        llvm::BasicBlock* CondBB =
            llvm::BasicBlock::Create(Ctx, "while.cond", MainFn);
        llvm::BasicBlock* BodyBB =
            llvm::BasicBlock::Create(Ctx, "while.body", MainFn);
        llvm::BasicBlock* AfterBB =
            llvm::BasicBlock::Create(Ctx, "while.end", MainFn);
        Builder.CreateBr(CondBB);
        Builder.SetInsertPoint(CondBB);
        Builder.CreateCondBr(buildCond(s.op, s.condA, s.condB, s.line_number),
                             BodyBB, AfterBB);
        Builder.SetInsertPoint(BodyBB);
        codegenBlock(s.body);
        if (!Builder.GetInsertBlock()->getTerminator())
            Builder.CreateBr(CondBB);
        Builder.SetInsertPoint(AfterBB);
        break;
    }
    case Stmt::Type::HOR: {
        auto it = SymbolTable.find(s.forVarName);
        if (it == SymbolTable.end() || it->second.type != VarType::INT) {
            reportError("Loop variable for 'hor' must be an integer.",
                        s.line_number);
        }

        TypedValue startVal_tv = buildExpr(s.forStart, true, s.line_number);
        TypedValue endVal_tv = buildExpr(s.forEnd, true, s.line_number);

        llvm::Value* startVal = startVal_tv.val;
        if (startVal_tv.type == VarType::FLOAT) {
            startVal = Builder.CreateFPToSI(startVal, I64, "cast.for");
        }
        llvm::Value* endVal = endVal_tv.val;
        if (endVal_tv.type == VarType::FLOAT) {
            endVal = Builder.CreateFPToSI(endVal, I64, "cast.for");
        }

        llvm::Value* loopVarIndexVal = nullptr;
        if (s.forVarIsArray) {
            TypedValue idx_tv =
                buildExpr(s.forVarIndexExpr, false, s.line_number);
            if (idx_tv.type == VarType::FLOAT) {
                reportError("Array index for 'hor' loop variable cannot be a "
                            "float.",
                            s.line_number);
            }
            loopVarIndexVal = idx_tv.val;
        }

        auto storeLoopVar = [&](llvm::Value* v) {
            if (s.forVarIsArray)
                storeArrayElem(s.forVarName, loopVarIndexVal, v);
            else
                storeScalar(s.forVarName, v);
        };
        auto loadLoopVar = [&]() {
            if (s.forVarIsArray) {
                return Builder.CreateLoad(
                    I64, getArrayElemPtr(s.forVarName, loopVarIndexVal),
                    s.forVarName + ".elem");
            }
            return Builder.CreateLoad(I64, it->second.allocaInst,
                                      s.forVarName + ".val");
        };

        storeLoopVar(startVal);

        llvm::BasicBlock* CondBB =
            llvm::BasicBlock::Create(Ctx, "for.cond", MainFn);
        llvm::BasicBlock* BodyBB =
            llvm::BasicBlock::Create(Ctx, "for.body", MainFn);
        llvm::BasicBlock* StepBB =
            llvm::BasicBlock::Create(Ctx, "for.inc", MainFn);
        llvm::BasicBlock* AfterBB =
            llvm::BasicBlock::Create(Ctx, "for.end", MainFn);

        Builder.CreateBr(CondBB);
        Builder.SetInsertPoint(CondBB);
        Builder.CreateCondBr(
            Builder.CreateICmpSLE(loadLoopVar(), endVal, "forcond"), BodyBB,
            AfterBB);

        Builder.SetInsertPoint(BodyBB);
        codegenBlock(s.body);
        if (!Builder.GetInsertBlock()->getTerminator())
            Builder.CreateBr(StepBB);

        Builder.SetInsertPoint(StepBB);
        storeLoopVar(Builder.CreateAdd(loadLoopVar(), C1_64, "inc"));
        Builder.CreateBr(CondBB);

        Builder.SetInsertPoint(AfterBB);
        llvm::BasicBlock* SetFinalVarBB =
            llvm::BasicBlock::Create(Ctx, "for.setfinal", MainFn);
        llvm::BasicBlock* FinalMergeBB =
            llvm::BasicBlock::Create(Ctx, "for.finalmerge", MainFn);
        Builder.CreateCondBr(
            Builder.CreateICmpSLE(startVal, endVal, "loopDidRun"),
            SetFinalVarBB, FinalMergeBB);

        Builder.SetInsertPoint(SetFinalVarBB);
        storeLoopVar(endVal);
        Builder.CreateBr(FinalMergeBB);

        Builder.SetInsertPoint(FinalMergeBB);
        break;
    }
    }
}

std::vector<std::string> read_lines_from_file(const std::string& filename) {
    std::ifstream ifs(filename);
    if (!ifs) {
        llvm::errs() << std::format("Error: cannot open input file {}\n",
                                    filename);
        std::exit(1);
    }
    std::vector<std::string> lines;
    std::string line;
    while (std::getline(ifs, line)) {
        std::size_t comment_pos = line.find('#');
        if (comment_pos != std::string::npos) {
            line = line.substr(0, comment_pos);
        }
        lines.push_back(line);
    }
    return lines;
}

int main(int argc, char** argv) {
    if (argc != 3) {
        llvm::errs() << std::format("Usage: {} <input.cyaron> <output.ll>\n",
                                    argv[0]);
        return 1;
    }
    std::string inputFile = argv[1];
    std::string outputFile = argv[2];

    auto lines = read_lines_from_file(inputFile);

    Parser parser(std::move(lines));
    Program program = parser.parse_program();

    CodeGenerator generator("CYaRonModule");
    generator.generate(program);
    generator.writeToFile(outputFile);

    return 0;
}
