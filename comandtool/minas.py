#-*- python -*-
#**********************************************************************************************************************
#
# RISC-V Minimum Assembler
#
# Copyright (C) 2019 Tsuneo Nakanishi and Tomoaki Ukezono (Fukuoka University)
#
# 更新履歴
# 1.00:
# - 初版
# 1.01:
# - sw コマンドのアセンブルに関するバグを修正。
# - コピペ対策バイナリを生成するようにした。
# 1.02:
# - %hi，%lo で16進定数を指定できるようにした。
# - 最後の行が改行ではなく，EOFで終わっていた場合に文法エラーが出るバグを修正した。
# 1.03:
# - 乗除算命令（M標準拡張仕様）に対応した。
#**********************************************************************************************************************

from datetime import datetime
import getpass
import os
import re
import struct
import sys
import time
import uuid
import zipfile

# ソースファイル名
asm_filename = ""

# アセンブル中の行番号
asm_line_number = 1

# ロケーション
binary_loc = 0

# エラーフラグ
error_flag = False

# ラベル辞書：
# 　ラベル名（小文字）をキー，アドレスを値とする辞書。
label_dict = {
        }

# レジスタ名辞書：
# 　レジスタ名（小文字）をキー，レジスタ番号を値とする辞書。
reg_dict = {
        "x0":0, "x1":1, "x2":2, "x3":3, "x4":4, "x5":5, "x6":6, "x7":7,
        "x8":8, "x9":9, "x10":10, "x11":11, "x12":12, "x13":13, "x14":14, "x15":15,
        "x16":16, "x17":17, "x18":18, "x19":19, "x20":20, "x21":21, "x22":22, "x23":23,
        "x24":24, "x25":25, "x26":26, "x27":27, "x28":28, "x29":29, "x30":30, "x31":31,
        "zero":0, "ra":1, "sp":2, "gp":3, "tp":4, "t0":5, "t1":6, "t2":7,
        "s0":8, "fp":8, "s1":9, "a0":10, "a1":11, "a2":12, "a3":13, "a4":14, "a5":15,
        "a6":16, "a7":17, "s2":18, "s3":19, "s4":20, "s5":21, "s6":22, "s7":23,
        "s8":24, "s9":25, "s10":26, "s11":27, "t3":28, "t4":29, "t5":30, "t6":31,
        }

# レジスタ対レジスタ算術論理演算命令辞書：
# 　ニーモニック名（小文字）をキー，オペコードを値とする辞書。
reg_reg_arith_dict = {
        "add"   : 0b0000000_00000_00000_000_00000_0110011,
        "sub"   : 0b0100000_00000_00000_000_00000_0110011,
        "and"   : 0b0000000_00000_00000_111_00000_0110011,
        "or"    : 0b0000000_00000_00000_110_00000_0110011,
        "xor"   : 0b0000000_00000_00000_100_00000_0110011,
        "slt"   : 0b0000000_00000_00000_010_00000_0110011,
        "sltu"  : 0b0000000_00000_00000_011_00000_0110011,
        "sll"   : 0b0000000_00000_00000_001_00000_0110011,
        "srl"   : 0b0000000_00000_00000_101_00000_0110011,
        "sra"   : 0b0100000_00000_00000_101_00000_0110011,
        "mul"   : 0b0000001_00000_00000_000_00000_0110011,
        "mulh"  : 0b0000001_00000_00000_001_00000_0110011,
        "mulhu" : 0b0000001_00000_00000_011_00000_0110011,
        "mulhsu": 0b0000001_00000_00000_000_00000_0110011,
        "div"   : 0b0000001_00000_00000_100_00000_0110011,
        "rem"   : 0b0000001_00000_00000_110_00000_0110011,
        "divu"  : 0b0000001_00000_00000_101_00000_0110011,
        "remu"  : 0b0000001_00000_00000_111_00000_0110011,
        }

# レジスタ対即値算術論理演算命令辞書：
# 　ニーモニック名（小文字）をキー，オペコードを値とする辞書。
reg_imm_arith_dict = {
        "addi" : 0b000000000000_00000_000_00000_0010011,
        "andi" : 0b000000000000_00000_111_00000_0010011,
        "ori"  : 0b000000000000_00000_110_00000_0010011,
        "xori" : 0b000000000000_00000_100_00000_0010011,
        "slti" : 0b000000000000_00000_010_00000_0010011,
        "sltiu": 0b000000000000_00000_011_00000_0010011,
        "jalr" : 0b000000000000_00000_000_00000_1100111,
        }

# 即値シフト命令辞書：
# 　ニーモニック名（小文字）をキー，オペコードを値とする辞書。
reg_imm_shift_dict = {
        "slli": 0b0000000_00000_00000_001_00000_0010011,
        "srli": 0b0000000_00000_00000_101_00000_0010011,
        "srai": 0b0100000_00000_00000_101_00000_0010011,
        }

# ロード／ストア命令辞書：
# 　ニーモニック名（小文字）をキー，オペコードを値とする辞書。
load_store_dict = {
        "lw"  : 0b000000000000_00000_010_00000_0000011,
        "lh"  : 0b000000000000_00000_001_00000_0000011,
        "lhu" : 0b000000000000_00000_101_00000_0000011,
        "lb"  : 0b000000000000_00000_000_00000_0000011,
        "lbu" : 0b000000000000_00000_100_00000_0000011,
        "sw"  : 0b0000000_00000_00000_010_00000_0100011,
        "sh"  : 0b0000000_00000_00000_001_00000_0100011, 
        "sb"  : 0b0000000_00000_00000_000_00000_0100011,
        }

# 即値転送命令辞書：
# 　ニーモニック名（小文字）をキー，オペコードを値とする辞書。
data_xfer_dict = {
        "lui"  : 0b0000000000000000000_00000_0110111,
        "auipc": 0b0000000000000000000_00000_0010111,
        }

# 条件分岐命令辞書：
# 　条件分岐命令のニーモニック名（小文字）をキー，オペコードを値とする辞書。
cond_branch_dict = {
        "beq" : 0b0_000000_00000_00000_000_0000_0_1100011,
        "bne" : 0b0_000000_00000_00000_001_0000_0_1100011,
        "blt" : 0b0_000000_00000_00000_100_0000_0_1100011,
        "bge" : 0b0_000000_00000_00000_101_0000_0_1100011,
        "bltu": 0b0_000000_00000_00000_110_0000_0_1100011,
        "bgeu": 0b0_000000_00000_00000_111_0000_0_1100011,
        }

# 予約語リスト：
# 　ラベル名として使用できない予約語を格納するリスト。
reserved_words = {}
for dict in [reg_dict, reg_reg_arith_dict, reg_imm_arith_dict, reg_imm_shift_dict, load_store_dict, data_xfer_dict, cond_branch_dict]:
        for kw in dict:
                reserved_words[kw] = None

#**********************************************************************************************************************
# 構文解析関数群
#**********************************************************************************************************************

# 文頭の正規文法（パターン）
beginning_pat = \
        r"^(?P<label>[A-Za-z_][0-9A-Za-z_]*:)?\s*"

# レジスタ対レジスタ算術論理演算命令の正規文法（パターン）
reg_reg_arith_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<rd>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<rs1>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<rs2>[A-Za-z][0-9A-Za-z]*)\s*$"

# レジスタ対即値算術論理演算命令の正規文法（パターン）
reg_imm_arith_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<rd>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<rs1>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"((?P<dec>[+-]?[0-9]+)|(?P<hex>0x[0-9A-Fa-f]+)|(%lo\((?P<ref>[A-Za-z_][0-9A-Za-z_]*)\))|(%lo\((?P<lohex>0x[0-9A-Fa-f]+)\)))\s*$"

# 即値シフト命令の正規文法（パターン）
reg_imm_shift_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<rd>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<rs1>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"((?P<dec>[+-]?[0-9]+)|(?P<hex>0x[0-9A-Fa-f]+))\s*$"

# ロード／ストア命令の正規文法（パターン）
load_store_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<reg>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"((?P<dec>[+-]?[0-9]+)|(?P<hex>0x[0-9A-Fa-f]+)|(%lo\((?P<ref>[A-Za-z_][0-9A-Za-z_]*)\))|(%lo(\(?P<lohex>0x[0-9A-Fa-f]+)\)))\s*" \
        r"\((?P<rs1>[A-Za-z][0-9A-Za-z]*)\)\s*$"

# データ転送命令の正規文法（パターン）
data_xfer_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<rd>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"((?P<dec>[+-]?[0-9]+)|(?P<hex>0x[0-9A-Fa-f]+)|(%hi\((?P<ref>[A-Za-z_][0-9A-Za-z_]*)\))|(%hi\((?P<hihex>0x[0-9A-Fa-f]+)\)))\s*$"

# 条件分岐命令の正規文法（パターン）
cond_branch_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        R"(?P<rs1>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<rs2>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<dest>[A-Za-z_][0-9A-Za-z_]*)$"

# jal 命令の正規文法（パターン）
jal_pat = \
        r"(?P<mnemonic>[A-Za-z]+)\s+" \
        r"(?P<rd>[A-Za-z][0-9A-Za-z]*)\s*,\s*" \
        r"(?P<dest>[A-Za-z_][0-9A-Za-z_]*)\s*$"

# データ定義疑似命令の正規文法（パターン）
defdata_pat = \
        r"(?P<directive>\.[A-Za-z]+)\s+" \
        r"(?P<datalist>(([+-]?[0-9]+)|(0x[0-9A-Fa-f]+)|([A-Za-z_][0-9A-Za-z_]*))(\s*,\s*(([+-]?[0-9]+)|(0x[0-9A-Fa-f]+)|([A-Za-z_][0-9A-Za-z_]*)))*)\s*$"

# 文字列定義疑似命令の正規文法（パターン）
cstr_pat = \
        r"(?P<directive>\.[A-Za-z]+)\s+" \
        r"\"(?P<str>[ !#-~]*)\"\s*$"

# ラベル文の正規文法（パターン）
label_pat = \
        r"^(?P<label>[A-Za-z_][0-9A-Za-z_]*:)\s*$"

# 空文の正規文法（パターン）
null_pat = \
        r"^\s*$"

# 各パターンをコンパイルする。
reg_reg_arith_pat = re.compile (beginning_pat + reg_reg_arith_pat)
reg_imm_arith_pat = re.compile (beginning_pat + reg_imm_arith_pat)
reg_imm_shift_pat = re.compile (beginning_pat + reg_imm_shift_pat)
load_store_pat = re.compile (beginning_pat + load_store_pat)
data_xfer_pat = re.compile (beginning_pat + data_xfer_pat)
cond_branch_pat = re.compile (beginning_pat + cond_branch_pat)
jal_pat = re.compile (beginning_pat + jal_pat)
defdata_pat = re.compile (beginning_pat + defdata_pat)
cstr_pat = re.compile (beginning_pat + cstr_pat)
label_pat = re.compile (label_pat)
null_pat = re.compile (null_pat)

# エラーメッセージを出力する。
# ファイル名を filename，エラー行番号を lineno，エラーメッセージを msg に指定する。

def print_error (filename, lineno, msg):
        print ("{0}, line {1}, {2}".format (filename, lineno, msg), file = sys.stderr)

# パディング量を返す。
def padding_size (unitsize):
        size = 0
        if binary_loc % unitsize != 0:
                size = unitsize - binary_loc % unitsize
        return size

# 指定量のパディングをする。
def insert_padding (padsize):
        global binary_loc
        for i in range (padsize):
                bin_file.write (struct.pack ('B', 0))
                binary_loc += 1
        
# レジスタ対レジスタ算術論理演算命令を解析する。

def parse_reg_reg_arith (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = reg_reg_arith_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = reg_reg_arith_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ディスティネーションレジスタを検証する。
        rdreg = match.group ('rd')
        rdindex = reg_dict.get (rdreg.lower ())
        if rdindex == None:
                print_error (asm_filename, asm_line_number, "不正なディスティネーションレジスタ {0} が指定されています。".format (rdreg))
                error_flag = True
        # ソースレジスタ1を検証する。
        rs1reg = match.group ('rs1')
        rs1index = reg_dict.get (rs1reg.lower ())
        if rs1index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # ソースレジスタ2を検証する。
        rs2reg = match.group ('rs2')
        rs2index = reg_dict.get (rs2reg.lower ())
        if rs2index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs2reg))
                error_flag = True
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                opcode |= ((rdindex << 7) | (rs1index << 15) | (rs2index << 20)) & 0xffffffff
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# レジスタ対レジスタ算術論理演算命令をパス1用に解析する。

def preparse_reg_reg_arith (asm_line):
        # マッチしなければ何もしない。
        match = reg_reg_arith_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# レジスタ対即値算術論理演算命令を解析する。

def parse_reg_imm_arith (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = reg_imm_arith_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = reg_imm_arith_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ディスティネーションレジスタを検証する。
        rdreg = match.group ('rd')
        rdindex = reg_dict.get (rdreg.lower ())
        if rdindex == None:
                print_error (asm_filename, asm_line_number, "不正なディスティネーションレジスタ {0} が指定されています。".format (rdreg))
                error_flag = True
        # ソースレジスタを検証する。
        rs1reg = match.group ('rs1')
        rs1index = reg_dict.get (rs1reg.lower ())
        if rs1index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # 即値を検証する。
        if match.group ('dec') != None:
                imm = int (match.group ('dec'))
                if mnemonic.lower () in { "addi", "slti", "jalr" }:
                        min = -2048
                        max = 2047
                if mnemonic.lower () in { "andi", "ori", "xori", "sltiu" }:
                        min = 0
                        max = 4095
                if (imm < min) or (imm > max):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（{0}～{1}）外の即値が指定されています。".format (min, max))
                        error_flag = True
        elif match.group ('hex') != None:
                imm = int (match.group ('hex'), 16)
                if (imm < 0) or (imm > 0xfff):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x000～0xfff）外の即値が指定されています。")
                        error_flag = True
        elif match.group ('ref') != None:
                ref = match.group ("ref")
                imm = label_dict.get (ref)
                if imm == None:
                        print_error (asm_filename, asm_line_number, "ラベル {0} は未定義です。".format (ref))
                        error_flag = True
                else:
                        imm &= 0x00000fff
        elif match.group ('lohex') != None:
                imm = int (match.group ('lohex'), 16)
                if (imm < 0) or (imm > 0xffffffff):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x00000000～0xffffffff）外の即値が指定されています。")
                        error_flag = True
                imm &= 0x00000fff
        else:
                pass
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                opcode |= ((rdindex << 7) | (rs1index << 15) | (imm << 20)) & 0xffffffff
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# レジスタ対即値算術論理演算命令のサイズを返す。

def preparse_reg_imm_arith (asm_line):
        # マッチしなければ何もしない。
        match = reg_imm_arith_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# 即値シフト命令を解析する。

def parse_reg_imm_shift (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = reg_imm_shift_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = reg_imm_shift_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ディスティネーションレジスタを検証する。
        rdreg = match.group ('rd')
        rdindex = reg_dict.get (rdreg.lower ())
        if rdindex == None:
                print_error (asm_filename, asm_line_number, "不正なディスティネーションレジスタ {0} が指定されています。".format (rdreg))
                error_flag = True
        # ソースレジスタを検証する。
        rs1reg = match.group ('rs1')
        rs1index = reg_dict.get (rs1reg.lower ())
        if rs1index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # シフト量を検証する。
        if match.group ('dec') != None:
                shamt = int (match.group ('dec'))
        elif match.group ('hex') != None:
                shamt = int (match.group ('hex'), 16)
        else:
                pass
        if (shamt < 0) or (shamt > 31):
                print_error (asm_filename, asm_line_number, "妥当な範囲（0～31）外のシフト量が指定されています。。")
                error_flag = True
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                opcode |= ((rdindex << 7) | (rs1index << 15) | (shamt << 20)) & 0xffffffff
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# 即値シフト命令のサイズを返す。

def preparse_reg_imm_shift (asm_line):
        # マッチしなければ何もしない。
        match = reg_imm_shift_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# ロード／ストア命令を解析する。

def parse_load_store (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        load_instructions = { "lw", "lh", "lhu", "lb", "lbu" }
        store_instructions = { "sw", "sh", "sb" }
        
        # マッチしなければ何もしない。
        match = load_store_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = load_store_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ロード／ストアの対象となるレジスタを検証する。
        reg = match.group ('reg')
        regindex = reg_dict.get (reg)
        if regindex == None:
                if mnemonic in load_instructions:
                        regtype = "ディスティネーションレジスタ"
                elif mnemonic in store_instructions:
                        regtype = "ソースレジスタ"
                else:
                        pass
                print_error (asm_filename, asm_line_number, "不正な{0} {1} が指定されています。".format (regtype, reg))
                error_flag = True
        # オフセットを検証する。
        if match.group ('dec') != None:
                imm = int (match.group ('dec'))
                if (imm < -2048) or (imm > 2047):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（-2048～2047）外の即値が指定されています。")
                        error_flag = True
        elif match.group ('hex') != None:
                imm = int (match.group ('hex'), 16)
                if imm > 0xfff:
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x000～0xfff）外の即値が指定されています。")
                        error_flag = True
        elif match.group ('ref') != None:
                ref = match.group ("ref")
                imm = label_dict.get (ref)
                if imm == None:
                        print_error (asm_filename, asm_line_number, "ラベル {0} は未定義です。".format (ref))
                        error_flag = True
                else:
                        imm &= 0x00000fff
        elif match.group ('lohex') != None:
                imm = match.group ("lohex")
                if (imm < 0x00000000) or (imm > 0xffffffff):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x00000000～0xffffffff）外の即値が指定されています。")
                        error_flag = True
                else:
                        imm &= 0x00000fff
        else:
                pass
        # インデックスレジスタを検証する。
        rs1reg = match.group ('rs1')
        rs1index = reg_dict.get (rs1reg.lower ())
        if rs1index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                if mnemonic in load_instructions:
                        opcode |= ((regindex << 7) | (rs1index << 15)) & 0xffffffff
                        opcode |= (imm << 20) & 0xffffffff
                elif mnemonic in store_instructions:
                        opcode |= ((regindex << 20) | (rs1index << 15)) & 0xffffffff
                        opcode |= ((imm & 0b00000000_00000000_00000000_00011111) << 7) & 0xffffffff
                        opcode |= ((imm & 0b00000000_00000000_00001111_11100000) << 20) & 0xffffffff
                else:
                        pass
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# ロード／ストア命令のサイズを返す。

def preparse_load_store (asm_line):
        # マッチしなければ何もしない。
        match = load_store_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# データ転送命令を解析する。

def parse_data_xfer (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = data_xfer_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = data_xfer_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ディスティネーションレジスタを検証する。
        rdreg = match.group ('rd')
        rdindex = reg_dict.get (rdreg.lower ())
        if rdindex == None:
                print_error (asm_filename, asm_line_number, "不正なディスティネーションレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # 即値を検証する。
        if match.group ('dec') != None:
                imm = int (match.group ('dec'))
                if (imm < 0) or (imm >= 1048576):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0～1048575）外の即値が指定されています。".format (imm))
                        error_flag = True
                else:
                        imm = (imm << 12) & 0xfffff000
        elif match.group ('hex') != None:
                imm = int (match.group ('hex'), 16)
                if imm >= 0x100000:
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x00000～0xfffff）外の即値が指定されています。".format (imm))
                        error_flag = True
                else:
                        imm = (imm << 12) & 0xfffff000
        elif match.group ('ref') != None:
                ref = match.group ("ref")
                imm = label_dict.get (ref)
                if imm == None:
                        print_error (asm_filename, asm_line_number, "ラベル {0} は未定義です。".format (ref))
                        error_flag = True
                else:
                        imm = imm & 0xfffff000
        elif match.group ('hihex') != None:
                imm = int (match.group ('hihex'), 16)
                if (imm < 0) or (imm > 0xffffffff):
                        print_error (asm_filename, asm_line_number, "妥当な範囲（0x00000000～0xffffffff）外の即値が指定されています。".format (imm))
                        error_flag = True
                else:
                        imm = imm & 0xfffff000
        else:
                pass
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                opcode |= (rdindex << 7) & 0xffffffff
                opcode |= (imm & 0xfffff000)
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# データ転送命令のサイズを返す。

def preparse_data_xfer (asm_line):
        # マッチしなければ何もしない。
        match = data_xfer_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# 条件分岐命令を解析する。

def parse_cond_branch (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = cond_branch_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        opcode = cond_branch_dict.get (mnemonic.lower ())
        if opcode == None:
                return None
        # ソースレジスタ1を検証する。
        rs1reg = match.group ('rs1')
        rs1index = reg_dict.get (rs1reg.lower ())
        if rs1index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # ソースレジスタ2を検証する。
        rs2reg = match.group ('rs2')
        rs2index = reg_dict.get (rs2reg.lower ())
        if rs2index == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs2reg))
                error_flag = True
        # 分岐先ラベルを検証する。
        dest = match.group ('dest')
        if dest.lower () in reserved_words:
                print_error (asm_filename, asm_line_number, "分岐先ラベルに予約語 {0} が指定されています。".format (dest))
                error_flag = True
                return None
        if label_dict.get (dest) == None:
                print_error (asm_filename, asm_line_number, "分岐先ラベル {0} を解決できません。".format (dest))
                error_flag = True
                return None
        jumpto = label_dict.get (dest)
        jumpto -= binary_loc
        if (jumpto < -4096) or (jumpto > 4094):
                print_error (asm_filename, asm_line_number, "分岐先ラベル {0} はジャンプ可能範囲外です。".format (dest))
                error_flag = True
                return None
        # コードを生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                if jumpto < 0:
                        jumpto += 8192
                opcode |= ((rs1index << 15) | (rs2index << 20)) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00000000_00011110) << 7) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00000111_11100000) << 20) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00001000_00000000) >> 4) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00010000_00000000) << 19) & 0xffffffff
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# 条件分岐命令のサイズを返す。

def preparse_cond_branch (asm_line):
        # マッチしなければ何もしない。
        match = cond_branch_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# jal 命令を解析する。

def parse_jal (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = jal_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        if label != None:
                label = label[:-1]
        # ニーモニックを検証する。
        mnemonic = match.group ('mnemonic')
        if mnemonic.lower () != "jal":
                return None
        # ディスティネーションレジスタを検証する。
        rdreg = match.group ('rd')
        rdindex = reg_dict.get (rdreg.lower ())
        if rdindex == None:
                print_error (asm_filename, asm_line_number, "不正なソースレジスタ {0} が指定されています。".format (rs1reg))
                error_flag = True
        # 分岐先ラベルを検証する。
        dest = match.group ('dest')
        if dest.lower () in reserved_words:
                print_error (asm_filename, asm_line_number, "分岐先ラベルに予約語 {0} が指定されています。".format (dest))
                error_flag = True
                return None
        jumpto = label_dict.get (dest)
        if  jumpto == None:
                print_error (asm_filename, asm_line_number, "分岐先ラベル {0} を解決できません。".format (dest))
                error_flag = True
                return None
        if (jumpto & 0xfff00000) != (binary_loc & 0xfff00000):
                print_error (asm_filename, asm_line_number, "分岐先ラベル {0} はジャンプ可能範囲外です。".format (dest))
                error_flag = True
                return None
        # コード生成する。
        if not error_flag:
                insert_padding (padding_size (4))
                opcode = 0b0_0000000000_0_00000000_00000_1101111
                opcode |= rdindex << 7;
                opcode |= ((jumpto & 0b00000000_00010000_00000000_00000000) << 11) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00001111_11110000_00000000)      ) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00001000_00000000) << 9) & 0xffffffff
                opcode |= ((jumpto & 0b00000000_00000000_00000111_11111110) << 20) & 0xffffffff
                bin_file.write (struct.pack ("<I", opcode))
                binary_loc += 4
        return True

# jal 命令のサイズを返す。

def preparse_jal (asm_line):
        # マッチしなければ何もしない。
        match = jal_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 4, padding_size (4))

# データ定義疑似命令を解析する。
def parse_defdata (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = defdata_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        if label != None:
                label = label[:-1]
        # ディレクティブを検証する。
        directive = match.group ('directive')
        if directive.lower () == ".dd":
                decmin = - 2**31
                decmax = + 2**31 - 1
                hexmax = 0xffffffff
                fmt = '<i'
                size = 4
        elif directive.lower () == ".dw":
                decmin = -32768
                decmax = +32767
                hexmax = 0xffff
                fmt = '<h'
                size = 2
        elif directive.lower () == ".db":
                decmin = -128
                decmax = +127
                hexmax = 0xff
                fmt = 'b'
                size = 1
        else:
                return None
        # コード生成する。
        if not error_flag:
                insert_padding (padding_size (size))
                datalist = match.group ('datalist')
                datalist = datalist.split (',')
                for data in datalist:
                        match = re.match ("^\s*((?P<dec>[+-]?[0-9]+)|(?P<hex>0x[0-9A-Fa-f]+)|(?P<ref>[A-Za-z_][0-9A-Za-z_]*))\s*$", data)
                        if match.group ('dec') != None:
                                dec = match.group ('dec')
                                data = int (dec)
                                if (data < decmin) or (data > decmax):
                                        print_error (asm_filename, asm_line_number, "データ {0} が {1} バイトで表現できる範囲を越えています。".format (dec, size))
                                        error_flag = True
                                        continue
                                bin_file.write (struct.pack (fmt, data))
                                binary_loc += size
                        elif match.group ('hex') != None:
                                hex = match.group ('hex')
                                data = int (hex, 16)
                                if data > hexmax:
                                        print_error (asm_filename, asm_line_number, "データ {0} が {1} バイトで表現できる範囲を越えています。".format (hex, size))
                                        error_flag = True
                                        continue
                                bin_file.write (struct.pack (fmt.upper (), data))
                                binary_loc += size
                        elif match.group ('ref') != None:
                                ref = match.group ('ref')
                                if directive.lower () != ".dd":
                                        print_error (asm_filename, asm_line_number, "ラベル {0} は {1} 疑似命令では指定できません。".format (ref, directive.lower ()))
                                        error_flag = True
                                        continue
                                data = label_dict.get (ref)
                                if data == None:
                                        print_error (asm_filename, asm_line_number, "ラベル {0} は未定義です。".format (ref))
                                        error_flag = True
                                        continue
                                bin_file.write (struct.pack (fmt, data))
                                binary_loc += size
        return True

# データ定義疑似命令のサイズを返す。

def preparse_defdata (asm_line):
        # マッチしなければ何もしない。
        match = defdata_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        # ディレクティブを検証する。
        directive = match.group ('directive')
        if directive.lower () == ".dd":
                unitsize = 4
        elif directive.lower () == ".dw":
                unitsize = 2
        elif directive.lower () == ".db":
                unitsize = 1
        else:
                return (False, None, 0, 0)
        datalist = match.group ('datalist')
        datalist = datalist.split (',')
        size = len (datalist) * unitsize
        return (True, label, size, padding_size (unitsize))

# 文字列定義疑似命令を解析する。

def parse_cstr (asm_line):
        global bin_file
        global binary_loc
        global error_flag
        # マッチしなければ何もしない。
        match = cstr_pat.search (asm_line)
        if not match:
                return None
        # ラベルを取得する。（検証はパス1で済んでいる。）
        label = match.group ('label')
        if label != None:
                label = label[:-1]
        # ディレクティブを検証する。
        directive = match.group ('directive')
        if directive.lower () != ".cstr":
                return None
        # コード生成する。
        if not error_flag:
                str = match.group ("str")
                for char in str:
                        bin_file.write (struct.pack ("B", ord (char)))
                        binary_loc += 1
                bin_file.write (struct.pack ("B", 0))
                binary_loc += 1
        return True

# 文字列定義疑似命令のサイズを返す。

def preparse_cstr (asm_line):
        # マッチしなければ何もしない。
        match = cstr_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        # コード生成する。
        str = match.group ("str")
        return (True, label, len (str) + 1, 0)

# ラベル文を解析する。

def parse_label (asm_line):
        # マッチしなければ何もしない。
        match = label_pat.search (asm_line)
        return match

# ラベルのみの文のサイズを返す。

def preparse_label (asm_line):
        # マッチしなければ何もしない。
        match = label_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        label = match.group ('label')
        return (True, label, 0, 0)

# 空文を解析する。

def parse_null (asm_line):
        # マッチしなければ何もしない。
        match = null_pat.search (asm_line)
        return match

# 空文のサイズを返す。

def preparse_null (asm_line):
        # マッチしなければ何もしない。
        match = null_pat.search (asm_line)
        if not match:
                return (False, None, 0, 0)
        # ラベルを取得する。
        return (True, None, 0, 0)

#**********************************************************************************************************************
# メインルーチン
#**********************************************************************************************************************

# 著作権を表示する。
print ("RISC-V Minimum Assembler Version 1.03", file = sys.stderr)
print ("Copyright (C) 2019 Tsuneo Nakanishi and Tomoaki Ukezono (Fukuoka University)", file = sys.stderr)
print (file = sys.stderr)

# ソースファイルをオープンする。
args = sys.argv
if len (args) < 2:
        print ("ソースファイルが指定されていません。", file = sys.stderr)
        sys.exit (1)
if len (args) > 2:
        print ("ソースファイルが複数指定されています。", file = sys.stderr)
        sys.exit (1)
asm_filename = args[1]
if not re.search (r'\.(s|asm)$', asm_filename.lower ()):
        print ("ソースファイル {0} の拡張子が不正です。".format (asm_filename), file = sys.stderr)
        sys.exit (1)
try:
	asm_file = open (asm_filename, "r")
except IOError:
        print ("ソースファイル {0} をオープンできません。".format (asm_filename), file = sys.stderr)
        sys.exit (1)

# オブジェクトファイルをオープンする。
bin_filename = re.sub (r'\.(s|asm)$', ".bin", asm_filename)
try:
	bin_file = open (bin_filename, "wb")
except IOError:
        print ("オブジェクトファイル {0} をオープンできません。".format (bin_filename), file = sys.stderr)
        sys.exit (1)

# ファイルヘッダを記録する。
bin_file.write (struct.pack ("8s", "FURV0000".encode ('utf-8'))) # マジックストリング
bin_file.write (struct.pack ("<I", 0x00000014)) # アセンブル環境情報
bin_file.write (struct.pack ("<I", 0x00000064)) # バイナリ
bin_file.write (struct.pack ("<I", 0x00000000)) # ソースコード

# アセンブル環境情報を記録する。
bin_file.write (struct.pack ("16s", uuid.uuid1 ().bytes)) # UUID1
bin_file.write (struct.pack ("16s", uuid.uuid4 ().bytes)) # UUID4
bin_file.write (struct.pack ("16s", getpass.getuser ().encode ('utf-8')[0:15])) # ユーザ名
bin_file.write (struct.pack ("<d", time.time ())) # アセンブル時刻
bin_file.write (struct.pack ("<d", os.stat (asm_filename).st_ctime)) # ファイル生成時刻
bin_file.write (struct.pack ("<d", os.stat (asm_filename).st_atime)) # ファイル参照時刻
bin_file.write (struct.pack ("<d", os.stat (asm_filename).st_mtime)) # ファイル更新時刻

# ラベルのアドレスを解決する。（パス1）
print ("*** PASS 1 ***", file = sys.stderr)
for asm_line in asm_file:
        # asm_line から最初の「#」以降のコメントを削除する。
        comment_pos = asm_line.find ('#')
        if comment_pos != -1:
                asm_line = asm_line[:comment_pos]
        else:
                asm_line = asm_line.rstrip (os.linesep)
        # 空行ならば次の文に進む。
        if len (asm_line) == 0:
                asm_line_number += 1
                continue
        # asm_line を構文解析する。
        for preparse in [preparse_reg_reg_arith, preparse_reg_imm_arith, preparse_reg_imm_shift, preparse_load_store, preparse_data_xfer, preparse_cond_branch, preparse_jal, preparse_defdata, preparse_cstr, preparse_label, preparse_null]:
                (ok, label, size, padding) = preparse (asm_line)
                if not ok:
                        continue
                binary_loc += padding
                if label != None:
                        label = label[:-1]
                        # ラベルに予約語が指定されているならエラーを出す。
                        if label.lower () in reserved_words:
                                print_error (asm_filename, asm_line_number, "ラベルに予約語 {0} が指定されています。".format (label))
                                error_flag = True
                                break
                        # ラベルが定義済みならエラーを出す。
                        if label_dict.get (label) != None:
                                print_error (asm_filename, asm_line_number, "ラベル {0} が重複定義されています。".format (label))
                                error_flag = True
                                break
                        # 当該ラベルに相当するアドレスを登録する。
                        label_dict[label] = binary_loc
                # カウンタを進める。
                binary_loc += size
                break
        else:
                print_error (asm_filename, asm_line_number, "文法エラー: {0}".format (asm_line))
                error_flag = True
        # 次の文に進む。
        asm_line_number += 1

# パス1でエラーが出ている場合は終了する。
if error_flag:
        print ("{0}, アセンブルに失敗しました。".format (asm_filename), file = sys.stderr)
        sys.exit (1)

# ソースコードを1行ずつ asm_line に読んで構文解析，コード生成する。（パス2）
print ("*** PASS 2 ***", file = sys.stderr)
asm_file.seek (0, 0)
asm_line_number = 1
binary_loc = 0
for asm_line in asm_file:
        # asm_line から最初の「#」以降のコメントを削除する。
        comment_pos = asm_line.find ('#')
        if comment_pos != -1:
                asm_line = asm_line[:comment_pos]
        else:
                asm_line = asm_line.rstrip (os.linesep)
        # 空行ならば次の文に進む。
        if len (asm_line) == 0:
                asm_line_number += 1
                continue
        # asm_line を構文解析する。
        for parse in [parse_reg_reg_arith, parse_reg_imm_arith, parse_reg_imm_shift, parse_load_store, parse_data_xfer, parse_cond_branch, parse_jal, parse_cstr, parse_defdata, parse_label, parse_null]:
                if parse (asm_line) != None:
                        break
        else:
                print_error (asm_filename, asm_line_number, "文法エラー: {0}".format (asm_line))
                error_flag = True
        # 次の文に進む。
        asm_line_number += 1

# ソースファイルをクローズする。
asm_file.close ()

# ソースコードを添付する。
pos = bin_file.tell ()
bin_file.seek (16, 0)
bin_file.write (struct.pack ("<I", pos))
bin_file.seek (pos, 0)

zip_filename = '$$$ZIPTMP$$$.zip'
with zipfile.ZipFile (zip_filename, 'w', compression = zipfile.ZIP_DEFLATED) as zipf:
        zipf.write (asm_filename, arcname = asm_filename)
with open (zip_filename, "rb") as zipf:
        while True:
                by = zipf.read (1)
                if not by:
                        break
                bin_file.write (by)
os.remove (zip_filename)

# オブジェクトファイルをクローズする。
bin_file.close ()

# エラー終了した場合は，途中まで生成していたオブジェクトファイルを削除する。
if error_flag:
        os.remove (bin_filename)
        print ("{0}, アセンブルに失敗しました。".format (asm_filename), file = sys.stderr)
        sys.exit (1)

# オブジェクトファイルの生成を報告する。
print ("{0}, オブジェクトファイル {1} を生成しました。".format (asm_filename, bin_filename), file = sys.stderr)

# ラベルのアドレスを出力する。
print ("*** Labels ***", file = sys.stderr)
for label in label_dict:
        print ("%-12s = 0x%08x" % (label, label_dict[label]), file = sys.stderr)

# 成功終了する。
sys.exit (0)
