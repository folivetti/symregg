from symregg import symregg_run, SymRegg
import pandas as pd

df = pd.read_csv("RAR.csv")
X = df.gbar.values
y = df.gobs.values
Xerr = df.e_gbar.values
yerr = df.e_gobs.values

reg = SymRegg(100, "BestFirst", 15, "add,sub,mul", "ROXY", 50, 2, -1, 1, "", "")
reg.fit(X, y, Xerr, yerr)
print(reg.results)
