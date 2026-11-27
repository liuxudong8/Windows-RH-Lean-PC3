import re

probe = r'C:\proj2\A5CharQ5\ProbeFive3.lean'
target = r'C:\proj2\A5CharQ5\ConjClasses.lean'

s = open(probe, encoding='utf-8').read()
i = s.index('-- (1)')
body = s[i:]

renames = [
    ('t1', 'G_centralizer_fiveCycle_eq_closure'),
    ('t2', 'G_class_fiveCycle_card'),
    ('t3', 'G_class_fiveCycle_set_card'),
    ('t4', 'G_fiveCycle_isConj_sG'),
]
for old, new in renames:
    body = re.sub(r'\b' + old + r'\b', new, body)

body = body.replace('-- (1) 任意 5-循环的中心化子 = ⟨g⟩',
                    '/-- **第 3 步推广**：任意 5-循环的中心化子 = ⟨g⟩。 -/')
body = body.replace('-- (2) 任意 5-循环的类大小 = 12',
                    '/-- **第 3 步推广**：任意 5-循环的类大小 = 12。 -/')
body = body.replace('-- (3) 类集合的基数 = 12',
                    '/-- **第 3 步推广**：任意 5-循环所在共轭类集合的基数 = 12。 -/')
body = body.replace('-- (4) {5} 类析取：任意 5-循环 与 sG 或 sG² 共轭',
                    '/-- **第 3 步收口**：任意 `{5}`-型元素与 `sG` 或 `sG ^ 2` 共轭。 -/')

with open(target, 'a', encoding='utf-8', newline='') as f:
    f.write('\n' + body)
print('appended', len(body), 'chars')
