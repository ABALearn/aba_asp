import os
import subprocess
import shutil
import datetime

sem = ["stb" ] #, "adm", "com", "prf", "grd"]
#csv = ["acute", "autism", "breastw", "krkp", "mushroom", "voting" ]
csv = ["breastw"]
time_limit = 300

for c in csv:
  for s in sem:
    for i in range(1, 2):
      cmd = "./cmdrunner \'swipl -g train -g halt aba_asp.pl configs/aamas2025_" + s + "_config.pl xabal/" + c + ".csv.f" + str(i) + ".pl\' " + str(time_limit)
      subprocess.call([cmd], shell=True)
      learnt_abaf = "xabal/" + c + ".csv.f" + str(i) + ".bk.sol"
      if os.path.exists(learnt_abaf + ".aba"):
        test_cmd = "swipl -g test -g halt aba_asp.pl configs/aamas2025_" + s + "_config.pl xabal/" + c + ".csv.f" + str(i) + ".pl"
        subprocess.call([test_cmd], shell=True)
        shutil.move(learnt_abaf + ".aba", learnt_abaf + "." + s + ".aba")
        if os.path.exists(learnt_abaf + ".asp"):
          shutil.move(learnt_abaf + ".asp", learnt_abaf + "." + s + ".asp")
        shutil.move(learnt_abaf + "_chk.asp", learnt_abaf + "_chk." + s + ".asp")
        shutil.move(learnt_abaf + ".test.csv", learnt_abaf + ".test." + s + ".csv" )        
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