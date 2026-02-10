import os
import subprocess
import shutil
import datetime
import glob

sem = ["stb", "adm", "com", "prf", "grd"]
csv = ["acute", "autism", "breastw", "krkp", "mushroom", "voting" ]
config="configs/lazy_"

for c in csv:
  for s in sem:
    for i in range(1, 6):
      learnt_abaf = "xabal/" + c + ".csv.f" + str(i) + ".bk.sol." + s
      if os.path.exists(learnt_abaf + ".aba"):
        print(learnt_abaf)
        test_cmd = "swipl -g listing\\(lopt/1\\) -g test\\(\\'" + learnt_abaf + "\\'\\) -g halt aba_asp.pl " + config + s + "_config.pl xabal/" + c + ".csv.f" + str(i) + ".pl"
        subprocess.call([test_cmd], shell=True)

pm_cmd = "swipl -g pm -g halt performance_eval.pl"
subprocess.call([pm_cmd], shell=True)

newpath = "xabal/PM"
if not os.path.exists(newpath):
  os.makedirs(newpath)

pattern = "*.PM.csv"
files_to_move = glob.glob("xabal/" + pattern)
for file in files_to_move:
  file_name = os.path.basename(file)
  shutil.move(file, "xabal/PM/" + file_name)

