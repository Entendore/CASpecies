import sys
import random
import math
from collections import deque, Counter
from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, 
                               QHBoxLayout, QPushButton, QSlider, QLabel, QButtonGroup, QComboBox)
from PySide6.QtCore import Qt, QTimer, QPoint, QRectF
from PySide6.QtGui import QPainter, QColor, QImage, QPen

# --- Ecosystem States ---
EMPTY = 0
WATER = 1
PLANT = 2
FUNGI = 3
CREATURE = 4
FIRE = 5
SNOW = 6
ALGAE = 7

WIND_VECTORS = [(0, -1), (1, -1), (1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1)]

class ALifeSim:
    def __init__(self, width, height):
        self.w = width
        self.h = height
        self.grid = [EMPTY] * (width * height)

        # Environment Grids
        self.nutrients = [0.5] * (width * height)
        self.fire_timer = [0] * (width * height)
        self.elevation = [0.0] * (width * height)
        self.moisture = [0.0] * (width * height)
        self.temperature = [0.5] * (width * height)
        self.scent = [0.0] * (width * height)
        self.alarm = [0.0] * (width * height)
        self.shelter = [0] * (width * height)
        self.plant_tox = [0.0] * (width * height)
        self.env_pathogen = [0.0] * (width * height)

        # Genome attributes
        self.energy = [0.0] * (width * height)
        self.age = [0] * (width * height)
        self.generation = [0] * (width * height)  # NEW: Track generations
        self.metabolism = [0.0] * (width * height)
        self.repro_thresh = [0.0] * (width * height)
        self.species_id = [0] * (width * height)
        self.diet_gene = [0.0] * (width * height)
        self.toxicity = [0.0] * (width * height)
        self.size = [1.0] * (width * height)
        self.camo = [0.0] * (width * height)
        self.max_age = [250] * (width * height)
        self.vision = [1] * (width * height)
        self.efficiency = [1.0] * (width * height)
        self.tolerance = [0.0] * (width * height)
        self.armor = [0.0] * (width * height)
        self.social = [0.0] * (width * height)
        self.aggression = [0.0] * (width * height)
        self.builder = [0.0] * (width * height)
        self.storage = [2.0] * (width * height)
        self.hibernate = [0.0] * (width * height)
        self.swimmer = [0.0] * (width * height)
        self.photosynth = [0.0] * (width * height)
        self.immunity = [0.0] * (width * height)
        self.mate = [0.0] * (width * height)

        self.infected = [0.0] * (width * height)

        self.moved = [False] * (width * height)
        self.indices = list(range(width * height))
        self.neighbors = self._get_neighbors(1)
        self.vision_2 = self._get_neighbors(2)
        self.vision_3 = self._get_neighbors(3)

        self.next_species_id = 0
        self.mutation_rate = 0.05
        self.disaster_rate = 0.002
        self.time_step = 0
        self.wind_dir = 0
        self.extinct_count = 0  # NEW: Track extinctions

        self.painted_herb_species = -1
        self.painted_carn_species = -1

        self.species_colors = {}
        self.init_life()

    def _get_neighbors(self, radius):
        neighbors = [[] for _ in range(self.w * self.h)]
        for y in range(self.h):
            for x in range(self.w):
                idx = y * self.w + x
                for dy in range(-radius, radius + 1):
                    for dx in range(-radius, radius + 1):
                        if max(abs(dx), abs(dy)) != radius: continue
                        nx, ny = (x + dx) % self.w, (y + dy) % self.h
                        neighbors[idx].append(ny * self.w + nx)
        return neighbors

    def get_season_multiplier(self):
        return 0.6 + 0.4 * math.sin(self.time_step / 200.0)

    def get_day_night_multiplier(self):
        return 0.5 + 0.5 * math.cos(self.time_step / 50.0)

    def register_species_color(self, sp_id, diet_gene, size, camo, toxicity):
        if sp_id in self.species_colors: return
        if toxicity > 0.5:
            c = QColor(255, 0, 255)
        else:
            h = (sp_id * 37) % 360
            s = int(255 * (1.0 - camo))
            v = int(100 + size * 60)
            if diet_gene > 0.6:
                v = max(50, v - 60)
            c = QColor.fromHsv(h, s, v)
        self.species_colors[sp_id] = (0xFF << 24) | (c.red() << 16) | (c.green() << 8) | c.blue()

    def init_life(self):
        self.time_step = 0
        self.next_species_id = 0
        self.extinct_count = 0  # Reset extinction counter
        self.species_colors.clear()
        self.wind_dir = 0

        seed1 = random.uniform(0, 10); seed2 = random.uniform(0, 10); seed3 = random.uniform(0, 10)
        for y in range(self.h):
            for x in range(self.w):
                idx = y * self.w + x
                e = 0.0
                e += math.sin(x * 0.05 + seed1) * math.cos(y * 0.05 + seed1) * 0.5
                e += math.sin(x * 0.1 + seed2) * math.cos(y * 0.1 + seed2) * 0.25
                e += math.sin(x * 0.2 + seed3) * math.cos(y * 0.2 + seed3) * 0.125
                self.elevation[idx] = max(0.0, min(1.0, e + 0.5))

        for i in range(self.w * self.h):
            self.grid[i] = EMPTY
            self.energy[i] = 0; self.age[i] = 0; self.generation[i] = 0; self.fire_timer[i] = 0
            self.scent[i] = 0.0; self.alarm[i] = 0.0; self.shelter[i] = 0
            self.infected[i] = 0.0; self.plant_tox[i] = 0.0; self.env_pathogen[i] = 0.0
            self.temperature[i] = 0.5

            if self.elevation[i] < 0.35:
                self.grid[i] = WATER; self.moisture[i] = 1.0; self.nutrients[i] = 0.0
            else:
                self.moisture[i] = random.uniform(0.3, 0.5); self.nutrients[i] = random.uniform(0.4, 0.8)

        sp1 = self.next_species_id; self.next_species_id += 1
        self.register_species_color(sp1, 0.0, 1.0, 0.0, 0.0)
        sp2 = self.next_species_id; self.next_species_id += 1
        self.register_species_color(sp2, 1.0, 1.5, 0.0, 0.0)
        self.painted_herb_species = sp1
        self.painted_carn_species = sp2

        for i in range(self.w * self.h):
            if self.grid[i] == WATER: continue
            r = random.random()
            if r < 0.15:
                self._spawn_creature(i, sp1, 0.0, 1.0, 20.0, 15.0, 0.0, 1.0, 0.0, 250, 1, 1.0, 0.5, 0.0, 0.3, 0.2, 0.2, 2.0, 0.2, 0.0, 0.0, 0.5, 0.5, 0)
            elif r < 0.17:
                self._spawn_creature(i, sp2, 1.0, 1.2, 35.0, 25.0, 0.0, 1.5, 0.0, 300, 2, 1.0, 0.5, 0.0, 0.5, 0.6, 0.2, 2.5, 0.2, 0.0, 0.0, 0.5, 0.2, 0)
            elif r < 0.5:
                self.grid[i] = PLANT; self.plant_tox[i] = random.uniform(0.0, 0.2)

    def _spawn_creature(self, idx, sp_id, diet, met, repro, en, tox, sz, cm, mxa, vis, eff, tol, arm, soc, agg, bld, stg, hib, swm, pho, imm, mt, gen=0):
        self.grid[idx] = CREATURE
        self.species_id[idx] = sp_id; self.diet_gene[idx] = diet; self.metabolism[idx] = met
        self.repro_thresh[idx] = repro; self.energy[idx] = en; self.age[idx] = 0
        self.toxicity[idx] = tox; self.size[idx] = sz; self.camo[idx] = cm
        self.max_age[idx] = mxa; self.vision[idx] = vis; self.efficiency[idx] = eff
        self.tolerance[idx] = tol; self.armor[idx] = arm
        self.social[idx] = soc; self.aggression[idx] = agg; self.builder[idx] = bld
        self.storage[idx] = stg; self.hibernate[idx] = hib
        self.swimmer[idx] = swm; self.photosynth[idx] = pho; self.immunity[idx] = imm
        self.mate[idx] = mt; self.infected[idx] = 0.0; self.generation[idx] = gen

    def paint_cell(self, x, y, state):
        if 0 <= x < self.w and 0 <= y < self.h:
            idx = y * self.w + x
            if state == "MOUNTAIN":
                self.elevation[idx] = min(1.0, self.elevation[idx] + 0.15)
                if self.elevation[idx] > 0.35 and self.grid[idx] == WATER:
                    self.grid[idx] = EMPTY; self.nutrients[idx] = 0.5; self.moisture[idx] = 0.4
            elif state == "VALLEY":
                self.elevation[idx] = max(0.0, self.elevation[idx] - 0.15)
                if self.elevation[idx] < 0.35 and self.grid[idx] != WATER:
                    self.grid[idx] = WATER; self.moisture[idx] = 1.0; self.nutrients[idx] = 0.0
            elif state == "DISEASE":
                self.env_pathogen[idx] = 1.0
                if self.grid[idx] == CREATURE: self.infected[idx] = 1.0
            elif state == CREATURE:
                if random.random() < 0.5:
                    self._spawn_creature(idx, self.painted_herb_species, 0.0, 1.0, 20.0, 30.0, 0.0, 1.0, 0.0, 250, 2, 1.0, 0.5, 0.0, 0.3, 0.2, 0.2, 2.0, 0.2, 0.0, 0.0, 0.5, 0.5, 0)
                else:
                    self._spawn_creature(idx, self.painted_carn_species, 1.0, 1.2, 35.0, 40.0, 0.0, 1.5, 0.0, 300, 2, 1.0, 0.5, 0.0, 0.5, 0.6, 0.2, 2.5, 0.2, 0.0, 0.0, 0.5, 0.2, 0)
            elif state == FIRE: self.grid[idx] = FIRE; self.fire_timer[idx] = 3
            elif state == WATER: self.grid[idx] = WATER; self.moisture[idx] = 1.0
            elif state == SNOW: self.grid[idx] = SNOW
            elif state == ALGAE: self.grid[idx] = ALGAE
            elif state == EMPTY: self.grid[idx] = EMPTY; self.energy[idx] = 0; self.shelter[idx] = 0
            else: self.grid[idx] = state

    def trigger_meteor(self):
        cx, cy = random.randint(0, self.w-1), random.randint(0, self.h-1)
        for dy in range(-2, 3):
            for dx in range(-2, 3):
                nx, ny = (cx + dx) % self.w, (cy + dy) % self.h
                idx = ny * self.w + nx
                dist = max(abs(dx), abs(dy))
                if dist <= 1:
                    self.grid[idx] = WATER; self.elevation[idx] = max(0.0, self.elevation[idx] - 0.5)
                    self.nutrients[idx] = 1.0; self.env_pathogen[idx] = 0.0
                elif dist == 2:
                    if self.grid[idx] != WATER:
                        self.grid[idx] = FIRE; self.fire_timer[idx] = 4
                    self.nutrients[idx] = 1.0

    def _kill_creature(self, i, leave_fungi=True):
        if self.elevation[i] < 0.35:
            self.grid[i] = WATER
        elif leave_fungi and random.random() < 0.6:
            self.grid[i] = FUNGI
            self.nutrients[i] = min(1.0, self.nutrients[i] + 0.3)
            self.plant_tox[i] = random.uniform(0.0, 0.3)
            if self.infected[i] > 0.5:
                self.plant_tox[i] = 0.8
                self.env_pathogen[i] = 1.0
        else:
            self.grid[i] = EMPTY
            self.nutrients[i] = min(1.0, self.nutrients[i] + 0.3)
        self.energy[i] = 0
        self.infected[i] = 0.0

    def step(self):
        self.time_step += 1
        self.moved = [False] * (self.w * self.h)
        random.shuffle(self.indices)

        if random.random() < self.disaster_rate:
            self.trigger_meteor()

        if self.time_step % 50 == 0:
            self.wind_dir = (self.wind_dir + random.randint(-1, 1)) % 8

        season_mult = self.get_season_multiplier()
        is_summer = season_mult > 0.8
        is_winter = season_mult < 0.4
        plant_growth = 0.02 * season_mult

        sun_mult = self.get_day_night_multiplier()
        is_night = sun_mult < 0.2

        for i in self.indices:
            if self.grid[i] == CREATURE:
                self.age[i] += 1
                if self.age[i] > self.max_age[i]:
                    death_chance = 0.02 * (self.age[i] - self.max_age[i])
                    if random.random() < death_chance:
                        self._kill_creature(i)

        # CA Step 1: Environment
        for i in self.indices:
            state = self.grid[i]
            x, y = i % self.w, i // self.w

            base_temp = season_mult
            altitude_penalty = max(0.0, (self.elevation[i] - 0.5) * 1.2)
            evap_cooling = self.moisture[i] * 0.2

            if self.shelter[i] == 1: self.temperature[i] = 0.5
            else: self.temperature[i] = max(0.0, min(1.0, base_temp - altitude_penalty - evap_cooling))
            is_freezing = self.temperature[i] < 0.2

            if self.time_step % 3 == 0:
                n = random.choice(self.neighbors[i])
                self.scent[i] = ((self.scent[i] + self.scent[n]) / 2.0) * 0.95
                self.alarm[i] = ((self.alarm[i] + self.alarm[n]) / 2.0) * 0.90
                self.env_pathogen[i] = ((self.env_pathogen[i] + self.env_pathogen[n]) / 2.0) * 0.99  # Slower decay

            if state not in (WATER, SNOW, ALGAE) and self.time_step % 3 == 0:
                n = random.choice(self.neighbors[i])
                avg_m = (self.moisture[i] + self.moisture[n]) / 2.0
                self.moisture[i] = avg_m
                if is_summer: self.moisture[i] = max(0.0, self.moisture[i] - 0.02)
                elif is_winter: self.moisture[i] = min(1.0, self.moisture[i] + 0.01)

            if state == WATER:
                if is_freezing and self.elevation[i] > 0.5 and random.random() < 0.1: self.grid[i] = SNOW
                elif not is_freezing and random.random() < 0.02:
                    if any(self.grid[n] == ALGAE for n in self.neighbors[i]): self.grid[i] = ALGAE
                else:
                    lowest_n = -1; lowest_elev = self.elevation[i]
                    for n in self.neighbors[i]:
                        if self.grid[n] in (EMPTY, PLANT, ALGAE) and self.elevation[n] < lowest_elev:
                            lowest_elev = self.elevation[n]; lowest_n = n
                    if lowest_n != -1 and random.random() < 0.2:
                        if self.grid[lowest_n] == CREATURE:
                            if self.swimmer[lowest_n] <= 0.5: self.grid[lowest_n] = WATER; self.energy[lowest_n] = 0
                        else: self.grid[lowest_n] = WATER; self.moisture[lowest_n] = 1.0
                        if self.elevation[i] > 0.4: self.grid[i] = EMPTY; self.moisture[i] = 0.8

            elif state == ALGAE:
                if is_summer and random.random() < 0.01: self.grid[i] = WATER
            elif state == SNOW:
                if not is_freezing: self.grid[i] = WATER; self.moisture[i] = 1.0
            elif state == FIRE:
                self.fire_timer[i] -= 1
                if self.fire_timer[i] <= 0:
                    self.grid[i] = EMPTY; self.nutrients[i] = min(1.0, self.nutrients[i] + 0.8); self.moisture[i] = 0.0
                    self.shelter[i] = 0
            elif state == PLANT:
                if is_summer and self.moisture[i] < 0.1 and self.nutrients[i] < 0.1 and random.random() < 0.01:
                    self.grid[i] = FIRE; self.fire_timer[i] = 3
                elif any(self.grid[n] == FIRE for n in self.neighbors[i]) and self.moisture[i] < 0.3:
                    self.grid[i] = FIRE; self.fire_timer[i] = 2
                else:
                    self.nutrients[i] = max(0.0, self.nutrients[i] - 0.002)
                    self.moisture[i] = max(0.0, self.moisture[i] - 0.005)
                    if (self.nutrients[i] <= 0.0 or self.moisture[i] <= 0.0) and random.random() < 0.05: self.grid[i] = EMPTY
            elif state == EMPTY:
                if self.time_step % 5 == 0:
                    n = random.choice(self.neighbors[i])
                    avg = (self.nutrients[i] + self.nutrients[n]) / 2.0
                    self.nutrients[i] = avg
                if self.nutrients[i] > 0.2 and self.moisture[i] > 0.2 and not is_freezing and not is_night:
                    if random.random() < plant_growth * (15 if any(self.grid[n]==PLANT for n in self.neighbors[i]) else 1):
                        self.grid[i] = PLANT; self.nutrients[i] -= 0.2; self.moisture[i] -= 0.1
                        plant_neighbors = [n for n in self.neighbors[i] if self.grid[n] == PLANT]
                        if plant_neighbors:
                            pn = random.choice(plant_neighbors)
                            self.plant_tox[i] = max(0.0, min(1.0, self.plant_tox[pn] + random.uniform(-0.1, 0.1)))
                        else: self.plant_tox[i] = 0.0
                elif self.nutrients[i] > 0.3 and self.moisture[i] > 0.3 and not is_freezing and not is_night:
                    dx, dy = WIND_VECTORS[self.wind_dir]
                    for dist in range(1, 4):
                        px, py = (x + dx * dist) % self.w, (y + dy * dist) % self.h
                        p_idx = py * self.w + px
                        if self.grid[p_idx] == PLANT and random.random() < 0.05:
                            self.grid[i] = PLANT; self.nutrients[i] -= 0.2
                            self.plant_tox[i] = max(0.0, min(1.0, self.plant_tox[p_idx] + random.uniform(-0.1, 0.1)))
                            break
                elif random.random() < 0.005:
                    if any(self.grid[n] == FUNGI for n in self.neighbors[i]): self.grid[i] = FUNGI
            elif state == FUNGI:
                self.nutrients[i] = min(1.0, self.nutrients[i] + 0.01)
                if random.random() < 0.01: self.grid[i] = EMPTY

        # CA Step 2: Creatures
        for i in self.indices:
            if self.moved[i]: continue
            state = self.grid[i]

            if state != CREATURE: continue

            if self.elevation[i] < 0.35 and self.swimmer[i] <= 0.5:
                self.energy[i] -= 20.0
                if self.energy[i] <= 0:
                    self._kill_creature(i); continue

            max_energy = self.repro_thresh[i] * self.storage[i]
            if self.photosynth[i] > 0.1 and self.elevation[i] >= 0.35 and not is_night:
                sun = self.get_season_multiplier()
                if sun > 0.4: self.energy[i] = min(max_energy, self.energy[i] + sun * self.photosynth[i] * 2.0)

            if self.infected[i] > 0:
                self.env_pathogen[i] = min(1.0, self.env_pathogen[i] + 0.02 * self.infected[i])  # Slower shedding
                self.energy[i] -= 5.0 * self.infected[i] * (1.0 - self.immunity[i])
                if random.random() < 0.02 * self.immunity[i]:
                    self.infected[i] = 0.0
                elif self.energy[i] <= 0:
                    self._kill_creature(i); continue
            elif self.env_pathogen[i] > 0.2 and self.env_pathogen[i] > self.immunity[i]:
                if random.random() < 0.05 * (self.env_pathogen[i] - self.immunity[i]):  # Slower infection
                    self.infected[i] = random.uniform(0.5, 1.0)

            temp_diff = abs(self.temperature[i] - self.tolerance[i])
            temp_penalty = 0.0 if self.shelter[i] == 1 else temp_diff * 1.5

            age_ratio = self.age[i] / max(1, self.max_age[i])
            is_juvenile = age_ratio < 0.25
            is_elder = age_ratio > 0.75
            can_reproduce = not is_juvenile and not is_elder

            eff_size = self.size[i] * (0.7 if is_juvenile else 1.3 if is_elder else 1.0)
            base_metabolism = (self.metabolism[i] * eff_size) + (self.age[i] * 0.005) + temp_penalty
            if is_juvenile: base_metabolism *= 1.2
            if is_elder: base_metabolism *= 0.8

            is_hibernating = is_winter and self.hibernate[i] > 0.5 and self.infected[i] == 0
            if is_hibernating:
                self.energy[i] -= base_metabolism * 0.1
                if self.energy[i] <= 0:
                    self._kill_creature(i); continue
                continue

            my_diet = self.diet_gene[i]
            can_eat_plants = my_diet <= 0.6
            can_eat_meat = my_diet >= 0.4
            is_omnivore = can_eat_plants and can_eat_meat

            my_vis = max(1, self.vision[i] - 1) if is_night else self.vision[i]
            if is_juvenile: my_vis += 1
            if is_elder: my_vis = max(1, my_vis - 1)

            my_species = self.species_id[i]
            acted = False
            is_hungry = self.energy[i] < max_energy * 0.8

            if temp_penalty > 0.5 and self.builder[i] > 0.5 and self.shelter[i] == 0 and random.random() < 0.2:
                self.shelter[i] = 1

            # 1. Fleeing
            threat_near = False
            if can_eat_plants:
                threats = [n for n in self.neighbors[i] if (self.grid[n] == CREATURE and self.diet_gene[n] >= 0.4) or self.grid[n] == FIRE]
                if not threats and my_vis >= 2:
                    threats = [n for n in self.vision_2[i] if (self.grid[n] == CREATURE and self.diet_gene[n] >= 0.4) or self.grid[n] == FIRE]
                if not threats and my_vis >= 3:
                    threats = [n for n in self.vision_3[i] if (self.grid[n] == CREATURE and self.diet_gene[n] >= 0.4) or self.grid[n] == FIRE]

                alarm_detected = self.alarm[i] > 0.2

                if threats or alarm_detected:
                    threat_near = True
                    self.alarm[i] = 1.0
                    if self.swimmer[i] > 0.5:
                        valid_targets = (EMPTY, PLANT, FUNGI, WATER, ALGAE)
                    else:
                        valid_targets = (EMPTY, PLANT, FUNGI, ALGAE)
                    safe_moves = []
                    for n in self.neighbors[i]:
                        if self.grid[n] in valid_targets and not self.moved[n]:
                            t_around = sum(1 for nn in self.neighbors[n] if (self.grid[nn] == CREATURE and self.diet_gene[nn] >= 0.4) or self.grid[nn] == FIRE)
                            score = t_around * 10 + self.alarm[n]
                            safe_moves.append((score, n))
                    if safe_moves:
                        safe_moves.sort(key=lambda x: x[0])
                        n = safe_moves[0][1]
                        gain = 12.0 if self.grid[n] == PLANT else 10.0 if self.grid[n] == ALGAE else 15.0 if self.grid[n] == FUNGI else 0
                        if is_omnivore: gain *= 0.8
                        tox_damage = self.plant_tox[n] * 20.0 * (1.0 - self.immunity[i]) if self.grid[n] == PLANT else 0
                        self.energy[i] = min(max_energy, self.energy[i] + gain * self.efficiency[i] - tox_damage)
                        self.energy[i] -= base_metabolism
                        if self.grid[n] in (PLANT, ALGAE, FUNGI): self.grid[n] = EMPTY
                        self._transfer_creature(i, n)
                        i = n; acted = True

            # 2. Hunting / Eating
            if not acted:
                targets = []
                if can_eat_plants:
                    targets.extend([n for n in self.neighbors[i] if self.grid[n] in (PLANT, ALGAE, FUNGI)])
                if can_eat_meat:
                    is_aggressive = self.aggression[i] > 0.5
                    for n in self.neighbors[i]:
                        if self.grid[n] == CREATURE and self.species_id[n] != my_species and not self.moved[n]:
                            if self.camo[n] >= my_vis: continue
                            if self.diet_gene[n] >= 0.4 and is_aggressive: targets.append(n)
                            elif self.size[n] < eff_size: targets.append(n)

                    if not targets and self.alarm[i] > 0.1:
                        move_targets = (EMPTY, PLANT, ALGAE, WATER) if self.swimmer[i] > 0.5 else (EMPTY, PLANT, ALGAE)
                        move_neighbors = [n for n in self.neighbors[i] if self.grid[n] in move_targets and not self.moved[n]]
                        best_n = max(move_neighbors, key=lambda n: self.alarm[n], default=-1)
                        if best_n != -1 and self.alarm[best_n] > self.alarm[i]:
                            if self.grid[best_n] == PLANT and can_eat_plants: 
                                tox_damage = self.plant_tox[best_n] * 20.0 * (1.0 - self.immunity[i])
                                gain = 12.0 * (0.8 if is_omnivore else 1.0)
                                self.energy[i] = min(max_energy, self.energy[i] + gain * self.efficiency[i] - tox_damage)
                                self.grid[best_n] = EMPTY
                            self._transfer_creature(i, best_n)
                            i = best_n; acted = True

                    if not targets and my_vis >= 2:
                        targets = [n for n in self.vision_2[i] if self.grid[n] == CREATURE and self.species_id[n] != my_species and self.size[n] < eff_size and self.camo[n] < my_vis]
                    if not targets and my_vis >= 3:
                        targets = [n for n in self.vision_3[i] if self.grid[n] == CREATURE and self.species_id[n] != my_species and self.size[n] < eff_size and self.camo[n] < my_vis]

                valid_targets = []
                for t in targets:
                    if self.grid[t] in (PLANT, ALGAE) and can_eat_plants: valid_targets.append(t)
                    elif self.grid[t] == FUNGI: valid_targets.append(t)
                    elif self.grid[t] == CREATURE and can_eat_meat: valid_targets.append(t)

                if valid_targets:
                    n = random.choice(valid_targets)
                    is_meat = self.grid[n] == CREATURE
                    is_fungi = self.grid[n] == FUNGI

                    if is_meat:
                        pack_size = sum(1 for nn in self.neighbors[i] if self.grid[nn] == CREATURE and self.species_id[nn] == my_species)
                        is_pack_hunting = pack_size >= 2 and self.social[i] > 0.5
                        if self.toxicity[n] > 0.5 and not is_pack_hunting:
                            self._kill_creature(i); continue
                        size_advantage = eff_size - self.size[n]
                        armor_block = self.armor[n] * max(0.1, 1.0 - size_advantage * 0.5)
                        if not is_pack_hunting and random.random() < armor_block:
                            self.energy[i] -= 2.0
                            if self.energy[i] <= 0:
                                self._kill_creature(i); continue
                            continue
                        self.alarm[n] = 1.0
                        gain = 20.0
                    elif is_fungi:
                        gain = 15.0
                        if not can_eat_plants: gain *= 0.5
                        if self.env_pathogen[n] > 0.5 and random.random() < 0.5:
                            self.infected[i] = random.uniform(0.5, 1.0)
                    else:
                        gain = 12.0 if self.grid[n] in (PLANT, ALGAE) else 15.0
                        tox_damage = self.plant_tox[n] * 20.0 * (1.0 - self.immunity[i]) if self.grid[n] == PLANT else 0
                        self.energy[i] = max(0, self.energy[i] - tox_damage)
                        if self.energy[i] <= 0:
                            self._kill_creature(i); continue

                    if is_omnivore and not is_fungi: gain *= 0.8

                    self.grid[n] = CREATURE
                    self.energy[n] = min(max_energy, self.energy[i] + (gain * self.efficiency[i]))
                    self._copy_genes(i, n)
                    self.grid[i] = WATER if self.elevation[i] < 0.35 else EMPTY
                    self.energy[i] = 0; self.moved[n] = True; i = n; acted = True
                    if not is_meat: self.scent[i] = 1.0

            # 3. Utility-Based Foraging & Resting
            if not acted:
                if not is_hungry and not threat_near and temp_penalty == 0:
                    rest_mult = 0.2 if is_night else 0.5  # Deep sleep at night
                    self.energy[i] -= base_metabolism * rest_mult
                    if self.energy[i] <= 0: self._kill_creature(i)
                    continue

                can_swim = self.swimmer[i] > 0.5
                valid_moves = (EMPTY, PLANT, ALGAE, FUNGI, WATER) if can_swim else (EMPTY, PLANT, ALGAE, FUNGI)
                
                move_neighbors = [n for n in self.neighbors[i] if self.grid[n] in valid_moves and not self.moved[n]]
                if move_neighbors:
                    scored_moves = []
                    for n in move_neighbors:
                        score = 0
                        if is_hungry:
                            if self.grid[n] == PLANT and can_eat_plants:
                                tox = self.plant_tox[n]
                                if self.immunity[i] < tox: score -= 50 * (tox - self.immunity[i])
                                else: score += 100
                            elif self.grid[n] == ALGAE and can_eat_plants: score += 100
                            elif self.grid[n] == FUNGI:
                                # Carnivores get desperate and seek fungi
                                score += 120 if not can_eat_plants else 80
                            
                            if can_eat_plants:
                                score += sum(20 for nn in self.neighbors[n] if self.grid[nn] in (PLANT, ALGAE))
                            if can_eat_meat:
                                score += sum(30 for nn in self.neighbors[n] if self.grid[nn] == CREATURE and self.species_id[nn] != my_species and self.size[nn] < eff_size)
                            
                            if can_eat_plants and self.scent[n] > self.scent[i]: score += self.scent[n] * 40
                            # Carnivores aggressively stalk alarm pheromones
                            if can_eat_meat and self.alarm[n] > self.alarm[i]: score += self.alarm[n] * 120

                            score += (self.nutrients[n] * 2.0) + (self.moisture[n] * 2.0)
                        
                        if self.env_pathogen[n] > 0.5: score -= 100
                        
                        if temp_penalty > 0.5:
                            if self.shelter[n] == 1: score += 200
                        
                        if self.social[i] > 0.5:
                            score += sum(5 for nn in self.neighbors[n] if self.grid[nn] == CREATURE and self.species_id[nn] == my_species)
                        
                        scored_moves.append((score, n))
                    
                    scored_moves.sort(key=lambda x: x[0], reverse=True)
                    n = scored_moves[0][1]
                    self.energy[i] -= base_metabolism
                    
                    if self.grid[n] == PLANT and can_eat_plants:
                        tox_damage = self.plant_tox[n] * 20.0 * (1.0 - self.immunity[i])
                        gain = 12.0 * (0.8 if is_omnivore else 1.0)
                        self.energy[i] = min(max_energy, self.energy[i] + gain * self.efficiency[i] - tox_damage)
                        self.grid[n] = EMPTY
                    elif self.grid[n] == ALGAE and can_eat_plants:
                        gain = 12.0 * (0.8 if is_omnivore else 1.0)
                        self.energy[i] = min(max_energy, self.energy[i] + gain * self.efficiency[i])
                        self.grid[n] = EMPTY
                    elif self.grid[n] == FUNGI:
                        gain = 15.0 * (0.5 if not can_eat_plants else 1.0) * (0.8 if is_omnivore else 1.0)
                        self.energy[i] = min(max_energy, self.energy[i] + gain * self.efficiency[i])
                        if self.env_pathogen[n] > 0.5 and random.random() < 0.5:
                            self.infected[i] = random.uniform(0.5, 1.0)
                        self.grid[n] = EMPTY
                        
                    if self.energy[i] <= 0:
                        self._kill_creature(i); continue
                    
                    self._transfer_creature(i, n)
                    i = n
                else:
                    self.energy[i] -= base_metabolism
                    if self.energy[i] <= 0: self._kill_creature(i)

            if self.grid[i] == CREATURE and self.infected[i] > 0:
                for n in self.neighbors[i]:
                    if self.grid[n] == CREATURE and self.infected[n] == 0:
                        if random.random() < 0.15 * self.infected[i] * (self.social[n] + 0.5) * (1.0 - self.immunity[n]):
                            self.infected[n] = random.uniform(0.5, 1.0)

            # 4. Reproduce
            if self.grid[i] == CREATURE and self.energy[i] >= self.repro_thresh[i] and self.infected[i] == 0 and can_reproduce:
                can_swim = self.swimmer[i] > 0.5
                empty_neighbors = [n for n in self.neighbors[i] if self.grid[n] == EMPTY and not self.moved[n]] if not can_swim else \
                                  [n for n in self.neighbors[i] if self.grid[n] in (EMPTY, WATER) and not self.moved[n]]
                if empty_neighbors:
                    n = random.choice(empty_neighbors)
                    partner_idx = -1
                    if self.mate[i] > 0.5:
                        partner_idx = next((pn for pn in self.neighbors[i] if self.grid[pn] == CREATURE and self.species_id[pn] == my_species and self.energy[pn] > self.repro_thresh[pn]*0.5), -1)
                    if self.mate[i] > 0.5 and partner_idx == -1: continue

                    new_sp = my_species; mutated = False
                    if random.random() < self.mutation_rate:
                        new_sp = self.next_species_id; self.next_species_id += 1; mutated = True

                    def mix_gene(gene_arr, idx1, idx2, mut_chance, min_val, max_val, mutate_fn=None):
                        v1 = gene_arr[idx1]; v2 = gene_arr[idx2] if partner_idx != -1 else gene_arr[idx1]
                        v = (v1 + v2) / 2.0
                        if random.random() < mut_chance:
                            v += random.uniform(-0.2, 0.2) if not mutate_fn else mutate_fn()
                        return max(min_val, min(max_val, v))

                    new_diet = mix_gene(self.diet_gene, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_met = mix_gene(self.metabolism, i, partner_idx, self.mutation_rate, 0.5, 3.0)
                    new_repro = mix_gene(self.repro_thresh, i, partner_idx, self.mutation_rate, 5.0, 50.0)
                    new_tox = mix_gene(self.toxicity, i, partner_idx, self.mutation_rate * 1.5, 0.0, 1.0)
                    new_sz = mix_gene(self.size, i, partner_idx, self.mutation_rate, 0.5, 2.5)
                    new_cm = mix_gene(self.camo, i, partner_idx, self.mutation_rate, 0.0, 0.9)
                    new_mxa = mix_gene(self.max_age, i, partner_idx, self.mutation_rate, 100, 500, mutate_fn=lambda: random.randint(-50, 50))
                    new_vis = self.vision[i] if random.random() >= self.mutation_rate else random.choice([1, 2, 3])
                    new_eff = mix_gene(self.efficiency, i, partner_idx, self.mutation_rate, 0.5, 1.5)
                    new_tol = mix_gene(self.tolerance, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_arm = mix_gene(self.armor, i, partner_idx, self.mutation_rate, 0.0, 0.9)
                    new_soc = mix_gene(self.social, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_agg = mix_gene(self.aggression, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_bld = mix_gene(self.builder, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_stg = mix_gene(self.storage, i, partner_idx, self.mutation_rate, 1.5, 5.0)
                    new_hib = mix_gene(self.hibernate, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_swm = mix_gene(self.swimmer, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_pho = mix_gene(self.photosynth, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_imm = mix_gene(self.immunity, i, partner_idx, self.mutation_rate, 0.0, 1.0)
                    new_mt = mix_gene(self.mate, i, partner_idx, self.mutation_rate, 0.0, 1.0)

                    if mutated: self.register_species_color(new_sp, new_diet, new_sz, new_cm, new_tox)
                    child_en = self.energy[i] / 2.0
                    self.energy[i] = self.energy[i] / 2.0
                    if partner_idx != -1:
                        child_en += self.energy[partner_idx] / 4.0
                        self.energy[partner_idx] = self.energy[partner_idx] * 0.75

                    new_gen = self.generation[i] + 1  # Increment generation
                    self._spawn_creature(n, new_sp, new_diet, new_met, new_repro, child_en, new_tox, new_sz, new_cm, new_mxa, new_vis, new_eff, new_tol, new_arm, new_soc, new_agg, new_bld, new_stg, new_hib, new_swm, new_pho, new_imm, new_mt, new_gen)
                    self.moved[n] = True

        # Extinction Tracking
        current_species = set()
        for i in self.indices:
            if self.grid[i] == CREATURE:
                current_species.add(self.species_id[i])
        
        for sp in list(self.species_colors.keys()):
            if sp not in current_species:
                self.extinct_count += 1
                del self.species_colors[sp]

    def _copy_genes(self, from_idx, to_idx):
        self.species_id[to_idx] = self.species_id[from_idx]
        self.diet_gene[to_idx] = self.diet_gene[from_idx]
        self.metabolism[to_idx] = self.metabolism[from_idx]
        self.repro_thresh[to_idx] = self.repro_thresh[from_idx]
        self.age[to_idx] = self.age[from_idx]
        self.generation[to_idx] = self.generation[from_idx]
        self.toxicity[to_idx] = self.toxicity[from_idx]
        self.size[to_idx] = self.size[from_idx]
        self.camo[to_idx] = self.camo[from_idx]
        self.max_age[to_idx] = self.max_age[from_idx]
        self.vision[to_idx] = self.vision[from_idx]
        self.efficiency[to_idx] = self.efficiency[from_idx]
        self.tolerance[to_idx] = self.tolerance[from_idx]
        self.armor[to_idx] = self.armor[from_idx]
        self.social[to_idx] = self.social[from_idx]
        self.aggression[to_idx] = self.aggression[from_idx]
        self.builder[to_idx] = self.builder[from_idx]
        self.storage[to_idx] = self.storage[from_idx]
        self.hibernate[to_idx] = self.hibernate[from_idx]
        self.swimmer[to_idx] = self.swimmer[from_idx]
        self.photosynth[to_idx] = self.photosynth[from_idx]
        self.immunity[to_idx] = self.immunity[from_idx]
        self.mate[to_idx] = self.mate[from_idx]
        self.infected[to_idx] = self.infected[from_idx]

    def _transfer_creature(self, from_idx, to_idx):
        self.grid[to_idx] = CREATURE
        self.energy[to_idx] = self.energy[from_idx]
        self.age[to_idx] = self.age[from_idx]
        self._copy_genes(from_idx, to_idx)
        self.grid[from_idx] = WATER if self.elevation[from_idx] < 0.35 else EMPTY
        self.energy[from_idx] = 0
        self.moved[to_idx] = True

    def get_cell_info(self, idx):
        state = self.grid[idx]
        if state == ALGAE: return {"state": state, "elevation": self.elevation[idx], "temperature": self.temperature[idx]}
        if state not in (CREATURE, EMPTY, PLANT): return None
        info = {
            "state": state, "nutrient": self.nutrients[idx], "elevation": self.elevation[idx], 
            "moisture": self.moisture[idx], "temperature": self.temperature[idx],
            "scent": self.scent[idx], "alarm": self.alarm[idx], "shelter": self.shelter[idx], "plant_tox": self.plant_tox[idx],
            "env_pathogen": self.env_pathogen[idx],
            "species": self.species_id[idx], "diet_gene": self.diet_gene[idx], "energy": self.energy[idx],
            "age": self.age[idx], "max_age": self.max_age[idx], "generation": self.generation[idx],
            "metabolism": self.metabolism[idx],
            "repro_thresh": self.repro_thresh[idx], "toxicity": self.toxicity[idx], "size": self.size[idx],
            "camo": self.camo[idx], "vision": self.vision[idx], "efficiency": self.efficiency[idx],
            "tolerance": self.tolerance[idx], "armor": self.armor[idx],
            "social": self.social[idx], "aggression": self.aggression[idx], "builder": self.builder[idx],
            "storage": self.storage[idx], "hibernate": self.hibernate[idx], "infected": self.infected[idx],
            "swimmer": self.swimmer[idx], "photosynth": self.photosynth[idx], "immunity": self.immunity[idx], "mate": self.mate[idx]
        }
        return info

class SimulationCanvas(QWidget):
    def __init__(self, sim):
        super().__init__()
        self.sim = sim
        self.setMinimumSize(600, 400)
        self.painting = False
        self.brush_state = PLANT
        self.setMouseTracking(True)
        self.hover_idx = -1
        self.render_mode = "Species"
        self.lut_empty = 0xFF1A1A1A
        self.lut_fungi = 0xFFFFA000
        self.lut_algae = 0xFF00695C

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform, False)
        w, h = self.sim.w, self.sim.h
        img = QImage(w, h, QImage.Format_RGB32)
        tick = self.sim.time_step
        sp_colors = self.sim.species_colors
        
        for i, state in enumerate(self.sim.grid):
            x, y = i % w, i // w
            if state == EMPTY: img.setPixel(x, y, self._get_env_color(i, "EMPTY"))
            elif state == PLANT: img.setPixel(x, y, self._get_env_color(i, "PLANT"))
            elif state == FUNGI: img.setPixel(x, y, self.lut_fungi)
            elif state == WATER:
                shimmer = math.sin(x*0.5 + y*0.5 + tick*0.1) * 15
                img.setPixel(x, y, 0xFF0A2A6E + int(shimmer))
            elif state == FIRE:
                flicker = random.randint(0, 50)
                img.setPixel(x, y, 0xFFFF8800 + flicker)
            elif state == SNOW: img.setPixel(x, y, 0xFFE0F7FA)
            elif state == ALGAE: img.setPixel(x, y, self.lut_algae)
            elif state == CREATURE: img.setPixel(x, y, self._get_creature_color(i))
            
            if self.sim.shelter[i] == 1 and state != CREATURE:
                img.setPixel(x, y, 0xFF4E342E)

        scaled_img = img.scaled(self.size(), Qt.KeepAspectRatio, Qt.FastTransformation)
        ox = (self.width() - scaled_img.width()) // 2
        oy = (self.height() - scaled_img.height()) // 2
        painter.drawImage(ox, oy, scaled_img)
        
        sun_mult = self.sim.get_day_night_multiplier()
        if sun_mult < 0.6:
            alpha = int((0.6 - sun_mult) * 255)
            painter.fillRect(ox, oy, scaled_img.width(), scaled_img.height(), QColor(10, 15, 40, alpha))
        
        if self.hover_idx != -1 and self.sim.grid[self.hover_idx] == CREATURE:
            self._draw_overlays(painter, scaled_img, ox, oy)

    def _get_env_color(self, i, state_type):
        mode = self.render_mode
        sim = self.sim
        if mode == "Topography":
            e = sim.elevation[i]
            if e < 0.35: return 0xFF1A237E 
            r = int(100 + e * 155); g = int(80 + e * 155); b = int(50 + e * 155)
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Moisture":
            m = sim.moisture[i]
            r = int(255 * (1.0 - m)); g = int(100 * (1.0 - m)); b = int(255 * m)
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Temperature":
            t = sim.temperature[i]
            r = int(255 * max(0, (t - 0.5) * 2)); g = int(255 * (1.0 - abs(t - 0.5) * 2)); b = int(255 * max(0, (0.5 - t) * 2))
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Soil" or mode == "Fire":
            n = sim.nutrients[i]
            r = int(255 * (1.0 - n)); g = int(200 * n); b = 0
            if mode == "Fire" and state_type == "PLANT": g = int(150 + (n * 105))
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Scent":
            s = sim.scent[i]
            r = 0; g = int(255 * s); b = int(255 * s)
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Alarm":
            a = sim.alarm[i]
            r = int(255 * a); g = 0; b = 0
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Pathogen":
            p = sim.env_pathogen[i]
            r = int(255 * p); g = int(50 * p); b = 0
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        else:
            if state_type == "PLANT":
                tox = sim.plant_tox[i]
                r = int(46 + tox * 100); g = int(125 - tox * 50); b = int(50 - tox * 30)
                return (0xFF << 24) | (r << 16) | (g << 8) | b
            e = sim.elevation[i]
            base_r = 26 + int(e * 40); base_g = 26 + int(e * 40); base_b = 26 + int(e * 40)
            return (0xFF << 24) | (base_r << 16) | (base_g << 8) | base_b

    def _get_creature_color(self, i):
        mode = self.render_mode
        sim = self.sim
        terrain_c = self._get_env_color(i, "EMPTY")
        if sim.shelter[i] == 1: terrain_c = 0xFF4E342E
        if mode in ("Soil", "Fire", "Topography", "Moisture", "Temperature", "Scent", "Alarm", "Pathogen"): return 0xFFFFFFFF 

        if mode == "Lineage": 
            return sp_colors.get(sim.species_id[i], 0xFFFFFFFF)
        
        if mode == "Generation":  # NEW RENDER MODE
            gen = sim.generation[i]
            ratio = min(1.0, gen / 50.0)  # Cap color mapping at gen 50
            r = int(255 * ratio); g = 0; b = int(255 * (1.0 - ratio))
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        
        if mode == "Health":
            if sim.infected[i] > 0:
                p = sim.infected[i]
                r = int(50 + 205 * p); g = int(200 - 100 * p); b = 0
                return (0xFF << 24) | (r << 16) | (g << 8) | b
            if sim.hibernate[i] > 0.5 and sim.get_season_multiplier() < 0.4: return 0xFF424242 
            return 0xFF00BCD4 

        if mode == "Life Stage":
            age_ratio = sim.age[i] / max(1, sim.max_age[i])
            if age_ratio < 0.25: return 0xFFFFEB3B
            elif age_ratio > 0.75: return 0xFFD32F2F
            else: return 0xFF00BCD4

        base_c = sp_colors.get(sim.species_id[i], 0xFFFFFFFF)
        if mode == "Species":
            ratio = min(1.0, sim.energy[i] / max(1.0, sim.repro_thresh[i] * sim.storage[i]))
            scale = 0.35 + 0.65 * ratio
            r = int(((base_c >> 16) & 0xFF) * scale); g = int(((base_c >> 8) & 0xFF) * scale); b = int((base_c & 0xFF) * scale)
            base_c = (0xFF << 24) | (r << 16) | (g << 8) | b
            camo_val = sim.camo[i]
            tr = (terrain_c >> 16) & 0xFF; tg = (terrain_c >> 8) & 0xFF; tb = terrain_c & 0xFF
            cr = (base_c >> 16) & 0xFF; cg = (base_c >> 8) & 0xFF; cb = base_c & 0xFF
            fr = int(cr * (1 - camo_val) + tr * camo_val); fg = int(cg * (1 - camo_val) + tg * camo_val); fb = int(cb * (1 - camo_val) + tb * camo_val)
            if sim.infected[i] > 0:
                fr = int(fr * 0.5 + 255 * 0.5); fg = int(fg * 0.5 + 0 * 0.5); fb = int(fb * 0.5 + 0 * 0.5)
            return (0xFF << 24) | (fr << 16) | (fg << 8) | fb
        elif mode == "Diet":
            d = sim.diet_gene[i]
            if d < 0.5: r = int(255 * (d * 2)); g = 255; b = 0
            else: r = 255; g = int(255 * ((1.0 - d) * 2)); b = 0
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Energy":
            e = min(1.0, sim.energy[i] / (sim.repro_thresh[i] * sim.storage[i]))
            r = int(255 * min(1.0, e * 2)); g = int(255 * max(0.0, (e - 0.5) * 2)); b = int(255 * max(0.0, (e - 0.8) * 5))
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Defense":
            r = int(255 * sim.toxicity[i]); g = 0; b = int(255 * sim.armor[i])
            v = 1.0 - (sim.camo[i] * 0.7)
            r = int(r * v); g = int(g * v); b = int(b * v)
            if r == 0 and g == 0 and b == 0: return 0xFF333333
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Size":
            s = (sim.size[i] - 0.5) / 2.0
            r = int(255 * s); g = 0; b = int(255 * (1.0 - s))
            return (0xFF << 24) | (r << 16) | (g << 8) | b
        elif mode == "Behavior":
            soc = sim.social[i]; agg = sim.aggression[i]; bld = sim.builder[i]; mt = sim.mate[i]
            if bld > 0.6: return 0xFF8D6E63 
            elif mt > 0.5: return 0xFFE91E63 
            elif soc > 0.5: return 0xFFFFEB3B 
            elif agg > 0.5: return 0xFFFF1744 
            else: return 0xFF424242 
        return 0xFFFFFFFF

    def _draw_overlays(self, painter, img, ox, oy):
        idx = self.hover_idx
        w, h = self.sim.w, self.sim.h
        vis = self.sim.vision[idx]
        rad = vis - 1
        px_w = img.width() / w; px_h = img.height() / h
        cx = (idx % w) * px_w + ox; cy = (idx // w) * px_h + oy
        rect_x = cx - (rad * px_w); rect_y = cy - (rad * px_h)
        rect_w = px_w * (rad * 2 + 1); rect_h = px_h * (rad * 2 + 1)
        painter.setPen(QPen(QColor(255, 255, 0, 200), 2))
        painter.setBrush(QColor(255, 255, 0, 40))
        painter.drawRect(QRectF(rect_x, rect_y, rect_w, rect_h))
        
        info = self.sim.get_cell_info(idx)
        d = info['diet_gene']
        diet_name = "Omnivore" if 0.4 <= d <= 0.6 else "Carnivore" if d > 0.6 else "Herbivore"
        status = "🤢 INFECTED" if info['infected'] > 0 else "Healthy"
        lines = [
            f"Sp: {info['species']} ({diet_name}) - {status}",
            f"Gen: {info['generation']} | En: {info['energy']:.1f}/{info['repro_thresh']*info['storage']:.1f}",
            f"Age: {info['age']}/{info['max_age']}",
            f"Vis: {info['vision']} | Sz: {info['size']:.2f}",
            f"Arm: {info['armor']:.2f} | Tox: {info['toxicity']:.2f}",
            f"Soc: {info['social']:.2f} | Agg: {info['aggression']:.2f}",
            f"Swm: {info['swimmer']:.2f} | Pho: {info['photosynth']:.2f}",
            f"Imm: {info['immunity']:.2f} | Mate: {info['mate']:.2f}"
        ]
        font = painter.font(); font.setPointSize(9); painter.setFont(font)
        fm = painter.fontMetrics()
        text_w = max(fm.horizontalAdvance(l) for l in lines) + 10
        text_h = len(lines) * 15 + 10
        tx = cx + 15; ty = cy + 15
        if ty + text_h > self.height(): ty = cy - text_h - 15
        if tx + text_w > self.width(): tx = cx - text_w - 15
        painter.setBrush(QColor(0, 0, 0, 200))
        painter.setPen(QPen(QColor(255, 255, 255), 1))
        painter.drawRect(QRectF(tx, ty, text_w, text_h))
        painter.setPen(QColor(255, 255, 255))
        for i, line in enumerate(lines): painter.drawText(QPoint(tx + 5, ty + 15 + (i * 15)), line)

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton: self.painting = True; self.paint_at(event.position())
    def mouseMoveEvent(self, event):
        self.update_hover(event.position())
        if self.painting: self.paint_at(event.position())
    def mouseReleaseEvent(self, event):
        if event.button() == Qt.LeftButton: self.painting = False
    def update_hover(self, pos):
        w, h = self.sim.w, self.sim.h
        aspect_sim = w / h; aspect_win = self.width() / self.height()
        if aspect_win > aspect_sim: draw_h = self.height(); draw_w = draw_h * aspect_sim
        else: draw_w = self.width(); draw_h = draw_w / aspect_sim
        offset_x = (self.width() - draw_w) / 2; offset_y = (self.height() - draw_h) / 2
        gx = int(((pos.x() - offset_x) / draw_w) * w); gy = int(((pos.y() - offset_y) / draw_h) * h)
        if 0 <= gx < w and 0 <= gy < h: self.hover_idx = gy * w + gx
        else: self.hover_idx = -1
        self.parent().parent().update_inspector(self.hover_idx)
        self.update()
    def paint_at(self, pos):
        w, h = self.sim.w, self.sim.h
        aspect_sim = w / h; aspect_win = self.width() / self.height()
        if aspect_win > aspect_sim: draw_h = self.height(); draw_w = draw_h * aspect_sim
        else: draw_w = self.width(); draw_h = draw_w / aspect_sim
        offset_x = (self.width() - draw_w) / 2; offset_y = (self.height() - draw_h) / 2
        gx = int(((pos.x() - offset_x) / draw_w) * w); gy = int(((pos.y() - offset_y) / draw_h) * h)
        for dy in range(-2, 3):
            for dx in range(-2, 3): self.sim.paint_cell(gx + dx, gy + dy, self.brush_state)
        self.update()

class GraphWidget(QWidget):
    def __init__(self):
        super().__init__()
        self.setMinimumHeight(100)
        self.history = deque(maxlen=200)
        self.max_val = 100
    def add_data(self, plants, herbi, omni, carn):
        self.history.append((plants, herbi, omni, carn))
        # FIX: Properly account for the 3x plant scaling when finding the max value
        current_max = max(max(data[0]/3.0, data[1], data[2], data[3]) for data in self.history) if self.history else 50
        self.max_val = max(50, current_max)
        self.update()
    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        painter.fillRect(self.rect(), QColor("#1E1E1E"))
        if len(self.history) < 2: return
        w, h = self.height(), self.width()  # Swap w and h conceptually just to use h for height properly
        w, h = self.width(), self.height()
        step_x = w / self.history.maxlen
        painter.setPen(QPen(QColor("#333333"), 1, Qt.DashLine))
        for i in range(1, 4):
            y = h * (i/4); painter.drawLine(0, y, w, y)
            
        # Draw dynamic max label
        painter.setPen(QColor("#666666"))
        painter.drawText(5, 15, f"Max: {int(self.max_val)}")

        colors = [QColor("#1B5E20"), QColor("#66BB6A"), QColor("#FFEB3B"), QColor("#EF5350")]
        for i in range(4):
            painter.setPen(QPen(colors[i], 2))
            path = []
            for idx, data in enumerate(self.history):
                x = idx * step_x
                # Normalize correctly based on the 3x scale for plants
                scale = 3 if i == 0 else 1
                norm = data[i] / (self.max_val * scale)
                norm = min(1.0, max(0.0, norm))  # Clamp strictly to 0.0 - 1.0
                y = h - (norm * h)
                path.append(QPoint(x, y))
            for p in range(len(path)-1): painter.drawLine(path[p], path[p+1])

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Ecosystem Viz - Macroevolution & Deep Time")
        self.resize(1000, 900)
        self.sim = ALifeSim(160, 120)
        
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setContentsMargins(10, 10, 10, 10)
        main_layout.setSpacing(8)
        
        top_ctrl = QHBoxLayout()
        self.btn_play = QPushButton("▶ Play"); self.btn_play.clicked.connect(self.toggle_play)
        self.btn_step = QPushButton("⏭ Step"); self.btn_step.clicked.connect(self.step_once)
        self.btn_reset = QPushButton("↻ Reset"); self.btn_reset.clicked.connect(self.reset_sim)
        self.btn_meteor = QPushButton("☄️ Strike"); self.btn_meteor.clicked.connect(self.sim.trigger_meteor)
        top_ctrl.addWidget(self.btn_play); top_ctrl.addWidget(self.btn_step); top_ctrl.addWidget(self.btn_reset); top_ctrl.addWidget(self.btn_meteor)
        top_ctrl.addStretch()
        
        top_ctrl.addWidget(QLabel("Render Mode:"))
        self.combo_render = QComboBox()
        self.combo_render.addItems(["Species", "Lineage", "Generation", "Diet", "Life Stage", "Energy", "Defense", "Size", "Soil", "Fire", "Topography", "Moisture", "Temperature", "Scent", "Alarm", "Pathogen", "Behavior", "Health"])
        self.combo_render.currentTextChanged.connect(self.change_render_mode)
        top_ctrl.addWidget(self.combo_render)
        top_ctrl.addStretch()
        
        top_ctrl.addWidget(QLabel("Brush:"))
        self.brush_buttons = QButtonGroup(self)
        for i, name in enumerate(["Eraser", "Plant", "Fungi", "Animal", "Water", "Fire", "Snow", "Algae", "Mtn", "Valley", "Disease"]):
            btn = QPushButton(name); btn.setCheckable(True)
            btn.clicked.connect(lambda checked, s=i: self.set_brush(s))
            self.brush_buttons.addButton(btn, i); top_ctrl.addWidget(btn)
            if name == "Plant": btn.setChecked(True)
        main_layout.addLayout(top_ctrl)
        
        self.canvas = SimulationCanvas(self.sim)
        self.canvas.brush_state = PLANT
        main_layout.addWidget(self.canvas, stretch=2)
        
        self.graph = GraphWidget()
        main_layout.addWidget(self.graph, stretch=1)
        
        bottom_ctrl = QHBoxLayout()
        self.lbl_speed = QLabel("Speed: 30ms")
        self.slider_speed = QSlider(Qt.Horizontal); self.slider_speed.setRange(10, 200); self.slider_speed.setValue(30)
        self.slider_speed.valueChanged.connect(self.update_speed)
        
        self.lbl_mut = QLabel("Mutation: 5%")
        self.slider_mut = QSlider(Qt.Horizontal); self.slider_mut.setRange(0, 20); self.slider_mut.setValue(5)
        self.slider_mut.valueChanged.connect(self.update_mut)

        self.lbl_dis = QLabel("Disaster: 0.2%")
        self.slider_dis = QSlider(Qt.Horizontal); self.slider_dis.setRange(0, 20); self.slider_dis.setValue(2)
        self.slider_dis.valueChanged.connect(self.update_dis)
        
        bottom_ctrl.addWidget(self.lbl_speed); bottom_ctrl.addWidget(self.slider_speed, stretch=1)
        bottom_ctrl.addWidget(self.lbl_mut); bottom_ctrl.addWidget(self.slider_mut, stretch=1)
        bottom_ctrl.addWidget(self.lbl_dis); bottom_ctrl.addWidget(self.slider_dis, stretch=1)
        main_layout.addLayout(bottom_ctrl)
        
        self.lbl_stats = QLabel("")
        self.lbl_stats.setAlignment(Qt.AlignCenter)
        self.lbl_stats.setStyleSheet("font-size: 13px; font-weight: bold; color: #ddd; padding: 5px; background-color: #222; border-radius: 4px;")
        main_layout.addWidget(self.lbl_stats)

        self.lbl_evolution = QLabel("ACTIVE LINEAGES: 0")
        self.lbl_evolution.setAlignment(Qt.AlignCenter)
        self.lbl_evolution.setStyleSheet("font-size: 12px; color: #ddd; padding: 5px; background-color: #222; border-radius: 4px;")
        main_layout.addWidget(self.lbl_evolution)

        self.lbl_inspector = QLabel("Hover over a creature to inspect its DNA...")
        self.lbl_inspector.setAlignment(Qt.AlignCenter)
        self.lbl_inspector.setStyleSheet("font-size: 12px; color: #00ff00; padding: 8px; background-color: #111; border: 1px solid #333; border-radius: 4px;")
        main_layout.addWidget(self.lbl_inspector)
        
        self.lbl_lineages = QLabel("TOP LINEAGES: None")
        self.lbl_lineages.setAlignment(Qt.AlignCenter)
        self.lbl_lineages.setStyleSheet("font-size: 12px; color: #aaa; padding: 5px; background-color: #222; border: 1px solid #333; border-radius: 4px;")
        main_layout.addWidget(self.lbl_lineages)

        self.timer = QTimer()
        self.timer.timeout.connect(self.step_once)
        self.update_speed()
        
        self.setStyleSheet("""
            QMainWindow { background-color: #121212; }
            QWidget { color: #d4d4d4; font-family: Arial; font-size: 13px; }
            QPushButton { background-color: #007acc; border: none; padding: 6px 12px; border-radius: 4px; color: white; font-weight: bold; }
            QPushButton:hover { background-color: #0098ff; }
            QPushButton:checked { background-color: #005a9e; border: 2px solid #00bcf2; }
            QComboBox { background-color: #007acc; border: none; padding: 4px 8px; border-radius: 4px; color: white; font-weight: bold; }
            QComboBox::drop-down { border: none; }
            QComboBox QAbstractItemView { background-color: #007acc; color: white; selection-background-color: #005a9e; }
            QSlider::groove:horizontal { border-radius: 3px; height: 6px; background: #333; }
            QSlider::handle:horizontal { background: #007acc; width: 14px; margin: -4px 0; border-radius: 7px; }
        """)
        self.update_stats()

    def change_render_mode(self, mode): self.canvas.render_mode = mode; self.canvas.update()
    def set_brush(self, state):
        state_map = [EMPTY, PLANT, FUNGI, CREATURE, WATER, FIRE, SNOW, ALGAE, "MOUNTAIN", "VALLEY", "DISEASE"]
        self.canvas.brush_state = state_map[state]
    def toggle_play(self):
        if self.timer.isActive(): self.timer.stop(); self.btn_play.setText("▶ Play")
        else: self.timer.start(); self.btn_play.setText("⏸ Pause")
    def step_once(self):
        self.sim.step(); self.canvas.update(); self.update_stats(); self.update_inspector(self.canvas.hover_idx)
    def reset_sim(self):
        self.sim.init_life(); self.canvas.update(); self.graph.history.clear(); self.update_stats()
    def update_speed(self):
        val = self.slider_speed.value(); self.lbl_speed.setText(f"Speed: {val}ms"); self.timer.setInterval(val)
    def update_mut(self):
        val = self.slider_mut.value(); self.sim.mutation_rate = val / 100.0; self.lbl_mut.setText(f"Mutation: {val}%")
    def update_dis(self):
        val = self.slider_dis.value(); self.sim.disaster_rate = val / 1000.0; self.lbl_dis.setText(f"Disaster: {val/10.0:.1f}%")
    def update_inspector(self, idx):
        if idx == -1: self.lbl_inspector.setText("Hover over grid to inspect..."); return
        info = self.sim.get_cell_info(idx)
        if not info: self.lbl_inspector.setText("Hover over grid to inspect..."); return
        if info['state'] != CREATURE:
            state_name = ['Empty', 'Water', 'Plant', 'Fungi', 'Creature', 'Fire', 'Snow', 'Algae'][info['state']]
            n = info.get('nutrient', 0); m = info.get('moisture', 0); e = info.get('elevation', 0); t = info.get('temperature', 0)
            s = info.get('scent', 0); a = info.get('alarm', 0); sh = "Yes" if info.get('shelter', 0)==1 else "No"; ptx = info.get('plant_tox', 0); pt = info.get('env_pathogen', 0)
            self.lbl_inspector.setText(f"Terrain -> State: {state_name}   |   🏔️ Elev: {e:.2f}   |   🌡️ Temp: {t:.2f}   |   💧 Moist: {m:.2f}   |   🌱 Soil: {n:.2f}   |   🐾 Scent: {s:.2f}   |   🚨 Alarm: {a:.2f}   |   🕳️ Shelter: {sh}   |   ☣️ PlantTox: {ptx:.2f}   |   🦠 Pathogen: {pt:.2f}")
            return
        d = info['diet_gene']
        diet_name = "Omnivore" if 0.4 <= d <= 0.6 else "Carnivore" if d > 0.6 else "Herbivore"
        is_toxic = "TOXIC" if info['toxicity'] > 0.5 else "Safe"
        in_shelter = "Yes" if info['shelter'] == 1 else "No"
        is_infected = "🤢 INFECTED" if info['infected'] > 0 else "Healthy"
        
        age_ratio = info['age'] / max(1, info['max_age'])
        stage = "Juvenile" if age_ratio < 0.25 else "Elder" if age_ratio > 0.75 else "Adult"

        self.lbl_inspector.setText(
            f"DNA -> Sp: {info['species']} ({diet_name} - {stage})   |   👁 Vis: {info['vision']}   |   📏 Sz: {info['size']:.2f}   |   🛡 Arm: {info['armor']:.2f}   |   🕵️ Camo: {info['camo']:.2f}   |   ☣️ Tox: {info['toxicity']:.2f} ({is_toxic})\n"
            f" ⚡ En: {info['energy']:.1f}/{info['repro_thresh']*info['storage']:.1f}   |   🕒 Age: {info['age']}/{info['max_age']}   |   🧬 Gen: {info['generation']}   |   🔥 Met: {info['metabolism']:.2f}   |   ⚙️ Eff: {info['efficiency']:.2f}   |   🌡️ Tol: {info['tolerance']:.2f}   |   👥 Soc: {info['social']:.2f}   |   ⚔️ Agg: {info['aggression']:.2f}\n"
            f" 🏔️ Elev: {info['elevation']:.2f}   |   🌡️ Temp: {info['temperature']:.2f}   |   💧 Moist: {info['moisture']:.2f}   |   🌱 Soil: {info['nutrient']:.2f}   |   🐾 Scent: {info['scent']:.2f}   |   🚨 Alarm: {info['alarm']:.2f}   |   🕳️ Shelter: {in_shelter}   |   🛌 Hib: {info['hibernate']:.2f}   |   {is_infected}\n"
            f" 🏊 Swim: {info['swimmer']:.2f}   |   ☀️ Photo: {info['photosynth']:.2f}   |   💊 Imm: {info['immunity']:.2f}   |   💖 Mate: {info['mate']:.2f}   |   🌿 PlantTox: {info['plant_tox']:.2f}   |   🦠 EnvPathogen: {info['env_pathogen']:.2f}   |   🧬 DietGene: {info['diet_gene']:.2f}"
        )
    def update_stats(self):
        counts = {EMPTY: 0, PLANT: 0, FUNGI: 0, CREATURE: 0, WATER: 0, FIRE: 0, SNOW: 0, ALGAE: 0}
        diets = {"Herb": 0, "Omni": 0, "Carn": 0}
        shelters = 0; infected_count = 0
        species_counts = Counter()
        species_sizes = {}
        max_gen = 0
        
        for i, state in enumerate(self.sim.grid):
            counts[state] = counts.get(state, 0) + 1
            if state == CREATURE: 
                d = self.sim.diet_gene[i]
                if d < 0.4: diets["Herb"] += 1
                elif d > 0.6: diets["Carn"] += 1
                else: diets["Omni"] += 1
                
                sp = self.sim.species_id[i]
                species_counts[sp] += 1
                if sp not in species_sizes: species_sizes[sp] = []
                species_sizes[sp].append(self.sim.size[i])
                if self.sim.infected[i] > 0: infected_count += 1
                if self.sim.generation[i] > max_gen: max_gen = self.sim.generation[i]
            if self.sim.shelter[i] == 1: shelters += 1

        season_mult = self.sim.get_season_multiplier()
        season_name = "Summer" if season_mult > 0.8 else "Winter" if season_mult < 0.4 else "Spring/Autumn"
        sun_mult = self.sim.get_day_night_multiplier()
        time_name = "Day" if sun_mult > 0.6 else "Night" if sun_mult < 0.2 else "Dusk/Dawn"

        self.lbl_stats.setText(f"🌱 Plants: {counts[PLANT]}   |   🌿 Algae: {counts[ALGAE]}   |   🍄 Fungi: {counts[FUNGI]}   |   🐾 Animals: {counts[CREATURE]}   |   🔥 Fires: {counts[FIRE]}   |   ❄️ Snow: {counts[SNOW]}   |   🕳️ Burrows: {shelters}   |   🤢 Infected: {infected_count}   |   ☀️ {season_name} / {time_name}")
        self.lbl_evolution.setText(f"ACTIVE LINEAGES: {len(species_counts)}   |   💀 EXTINCTIONS: {self.sim.extinct_count}   |   🧬 MAX GEN: {max_gen}   |   🐄 Herb: {diets['Herb']}   |   🐖 Omni: {diets['Omni']}   |   🐺 Carn: {diets['Carn']}")
        
        top_5 = species_counts.most_common(5)
        lin_str = "TOP LINEAGES:  "
        for sp, count in top_5:
            avg_sz = sum(species_sizes[sp]) / len(species_sizes[sp]) if species_sizes[sp] else 0
            lin_str += f"[Sp {sp} (Pop: {count}, Sz: {avg_sz:.1f})]  "
        self.lbl_lineages.setText(lin_str.strip())
        
        self.graph.add_data(counts[PLANT] + counts[ALGAE], diets["Herb"], diets["Omni"], diets["Carn"])

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = MainWindow()
    window.show()
    sys.exit(app.exec())