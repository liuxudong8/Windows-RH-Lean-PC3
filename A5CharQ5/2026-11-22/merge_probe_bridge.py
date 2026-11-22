probe = r'C:\proj2\A5CharQ5\ProbeCharBridge.lean'
target = r'C:\proj2\A5CharQ5\A5Defs.lean'

s = open(probe, encoding='utf-8').read()
body = s[s.index('-- (1)'):]

body = body.replace('-- (1) χ(sG⁻¹) = ᾱ',
                    '/-- χ(sG⁻¹) = ᾱ = 1 - α（sG⁻¹ = sG⁴）。 -/')
body = body.replace('-- (2) IsConj 推 char 相等',
                    '/-- 共轭元有相同的特征标值（`char_conj` 的 `IsConj` 形式）。 -/')

with open(target, 'a', encoding='utf-8', newline='') as f:
    f.write('\n' + body)
print('appended', len(body), 'chars')
