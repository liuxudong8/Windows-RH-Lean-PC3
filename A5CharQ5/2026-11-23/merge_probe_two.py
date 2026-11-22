probe = r'C:\proj2\A5CharQ5\ProbeTwoTwoCount.lean'
target = r'C:\proj2\A5CharQ5\ConjClasses.lean'

s = open(probe, encoding='utf-8').read()
body = s[s.index('-- (a)'):]

body = body.replace(
    '-- (a) S₅ 层 {2,2} 类大小 = 15（120 / 8）\nexample : Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by',
    '/-- **第 3 步**：S₅ 层 `{2,2}` 类大小 = 15（`120 / 8`）。 -/\ntheorem perm_twoTwo_count :\n    Nat.card {h : Equiv.Perm (Fin 5) | h.cycleType = {2,2}} = 15 := by')

body = body.replace(
    '-- (b) A₅ 层 {2,2} 类大小 = 15（双换位全偶，A₅ 与 S₅ 一致）\nexample : Nat.card {g : ↥G | g.val.cycleType = {2,2}} = 15 := by',
    '/-- **第 3 步**：A₅ 层 `{2,2}` 类大小 = 15（双换位全偶，故 A₅ 与 S₅ 的该类是同一批）。 -/\ntheorem G_twoTwo_set_card :\n    Nat.card {g : ↥G | g.val.cycleType = {2,2}} = 15 := by')

with open(target, 'a', encoding='utf-8', newline='') as f:
    f.write('\n' + body)
print('appended', len(body), 'chars')
