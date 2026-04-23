import os
import subprocess
import shutil
import datetime
import sys
import glob

sem = ["stb"]#, "adm", "com", "grd", "prf"]
time_limit = 300
config="configs/lazy_"
goals = glob.glob("./lib/abagen/abalp/*.bk.*.pl")

for f in goals:
  for s in sem:
      cmd = "./cmdrunner \'swipl -g halt aba_asp.pl " + config + s + "_config.pl " + f + "\' " + str(time_limit)
      #subprocess.call([cmd], shell=True)
      print(cmd)

sys.exit()