import os
import subprocess
import shutil
import datetime

sem = ["grd", "stb", "adm", "com", "prf"]
csv = ["breastw", "krkp", "mushroom", "autism", "acute", "voting" ]
time_limit = 900
config="configs/lazy_"

for c in csv:
  for s in sem:
    for i in range(1, 6):
      cmd = "./cmdrunner \'swipl -g train -g halt aba_asp.pl " + config + s + "_config.pl xabal/" + c + ".csv.f" + str(i) + ".pl\' " + str(time_limit)
      subprocess.call([cmd], shell=True)
      learnt_abaf = "xabal/" + c + ".csv.f" + str(i) + ".bk.sol"
      if os.path.exists(learnt_abaf + ".aba"):
        shutil.move(learnt_abaf + ".aba", learnt_abaf + "." + s + ".aba")
        if os.path.exists(learnt_abaf + ".asp"):
          shutil.move(learnt_abaf + ".asp", learnt_abaf + "." + s + ".asp")
        if os.path.exists(learnt_abaf + "_chk.asp"):  
          shutil.move(learnt_abaf + "_chk.asp", learnt_abaf + "_chk." + s + ".asp")  
      else:
        with open('aba_asp.csv', "a") as f:
          f.write(datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S,"))
          f.write(c + ".csv.bk,")
          f.write(s + ",")
          f.write("\'\\N\',")
          f.write("\'\\N\',")
          f.write("\'\\N\',")
          f.write("\'\\N\',")
          f.write("to\n")