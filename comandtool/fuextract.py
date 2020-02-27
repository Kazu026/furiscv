#-*- python -*-
#**********************************************************************************************************************
#
# FUExtract
#
# Copyright (C) 2019 Tsuneo Nakanishi (Fukuoka University)
#
#**********************************************************************************************************************

import datetime
import os
import re
import struct
import sys
import time
import uuid
import zipfile

# ソースファイルをオープンする。
args = sys.argv
if len (args) < 2:
        print ("ソースファイルが指定されていません。", file = sys.stderr)
        sys.exit (1)
if len (args) > 3:
        print ("ソースファイルが複数指定されています。", file = sys.stderr)
        sys.exit (1)
bin_filename = args[1]
try:
	bin_file = open (bin_filename, "rb")
except IOError:
        print ("ファイル {0} をオープンできません。".format (bin_filename), file = sys.stderr)
        sys.exit (1)

(magic, header_pos, binfile_pos, asmfile_pos) = struct.unpack ("8sIII", bin_file.read (20))

bin_file.seek (header_pos, 0)
uuid1 = struct.unpack ("16s", bin_file.read (16))[0]
uuid4 = struct.unpack ("16s", bin_file.read (16))[0]
username = struct.unpack ("16s", bin_file.read (16))
(asmtime, ctime, atime, mtime) = struct.unpack ("4d", bin_file.read (32))
print ("アセンブルユーザ： ", username[0].decode ('utf-8'))
print ("UUID1           ： ", uuid.UUID (bytes = uuid1))
print ("UUID4           ： ", uuid.UUID (bytes = uuid4))
print ("アセンブル日時　： ", time.strftime ("%Y-%m-%d %H:%M:%S", time.localtime (asmtime)))
print ("ファイル生成日時： ", time.strftime ("%Y-%m-%d %H:%M:%S", time.localtime (ctime)))
print ("ファイル参照日時： ", time.strftime ("%Y-%m-%d %H:%M:%S", time.localtime (atime)))
print ("ファイル更新日時： ", time.strftime ("%Y-%m-%d %H:%M:%S", time.localtime (mtime)))

destdir = os.sys.argv[2]
with open ("$$$out$$$.zip", "wb") as out_file:
    while True:
        by = bin_file.read (1)
        if not by:
            break
        out_file.write (by)
with zipfile.ZipFile('$$$out$$$.zip') as zipf:
    zipf.extractall (destdir)
os.remove ("$$$out$$$.zip")
sys.exit (0)
