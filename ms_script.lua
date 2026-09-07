-- MINESWEEPER SOLVER (zadey)

local Players          = game:GetService("Players")
local UserInputService = game:GetService("UserInputService")

if _G._msSolverStop then _G._msSolverStop() end
local _stopped = false
_G._msSolverStop = function() _stopped = true end

local _pg = Players.LocalPlayer:FindFirstChildOfClass("PlayerGui")
if _pg then
    local _old = _pg:FindFirstChild("MinesweeperSolverGui")
    if _old then _old:Destroy() end
end

local Settings = {
    Enabled           = true,
    AutoFlag          = false,
    AutoFlagCooldown  = 0.15,
    AutoReveal        = false,
    AutoRevealDelay   = 0.05, -- Default delay (0.00 to 0.20 range)
    AutoFlagRange     = 30,    -- Studs from player; outside this, don't auto-flag (0 to 100 range)
    DumbassMode       = false, -- Walk after another player (no CFrame teleporting)
    FollowTarget      = nil,   -- Player name picked in the dropdown
    FollowDistance    = 6,     -- Stop walking once this close to the target
    GuiEnabled        = true,
    GuessHelper       = true,
    SolverTickRate    = 0.15,
    IdleSleepCap      = 0.6,   -- Max sleep when the board is fully idle (CPU saver)
    IdleSleepAfter    = 6,     -- Solver ticks of inactivity before ramping the sleep up
    MaxVisibleHL      = 24,    -- Cap simultaneous SelectionBoxes (low-end GPU saver)
    HighlightRange    = 60,    -- Studs from player; outside this, hide outline
    PlanGuardLimit    = 16,    -- Down from 64 — large boards stall otherwise
    ContradictionCap  = 12,    -- Down from 15 — frontier explosion guard
    GridCheckInterval = 1.0,
    FlagRecheckEvery  = 8,     -- Recheck flagged cells once per N solver ticks
    ContradictionLoops = 10,   -- Inner propagation passes per contradiction test
    GuiUpdateInterval = 0.1,   -- Min seconds between status HUD refreshes
    BorderMoveThreshold = 1.5, -- Studs the player must move to force a border redraw
    RevealHoverHeight = 2,     -- Studs above the tile surface to teleport before stomping
    StompVelocity     = -150,  -- Downward velocity applied to trigger the tile collision
    BoardRootName     = "Flag",
    PartsFolderName   = "Parts",
    GuessDensityPrior = 0.20,  -- Blind mine density used when no adjacent number constrains a cell
    RiskWarnThreshold = 0.45,  -- Best-guess risk above this is flagged as a risky 50/50 in the HUD
    AutoDiscover      = true,  -- If BoardRootName is missing, scan the Workspace for a likely board
}

-- Allow overriding every setting without editing the source: set _G.MinesweeperConfig
-- before executing. Unknown keys are ignored so a config stays forward-compatible.
for _k, _v in pairs(_G.MinesweeperConfig or {}) do
    if Settings[_k] ~= nil then Settings[_k] = _v end
end

local data = {
    cells = {
        grid     = {},
        numbered = {},  -- persistent: terminal number cells (append-only between rebuilds)
        covered  = {},  -- persistent: unknown+covered cells (the per-tick scan frontier)
        flagged  = {},  -- persistent: flagged cells (rechecked periodically)
        toFlag   = {},
        toClear  = {},
    },
    toFlagCount   = 0,  -- kept alongside toFlag/toClear so the HUD never re-walks the sets
    toClearCount  = 0,
    tickCounter   = 0,
    grid = { w = 0, h = 0 },
    lastPartCount  = -1,
    statusGui      = nil,
    statusLabel    = nil,
    autoFlagBtn    = nil,
    autoRevealBtn  = nil,
    followBtn      = nil,
    followBlocked  = false,
    sliderLabel    = nil,
    sliderFill     = nil,
    rangeLabel     = nil,
    rangeFill      = nil,
    lastGuiUpdate  = 0,
    bestGuessCell  = nil,
    bestGuessScore = nil,
    lastBorderPos  = nil,  -- player pos at last border redraw (movement throttle)
}

local SAFE_COLOR  = Color3.fromRGB(0, 255, 0)
local MINE_COLOR  = Color3.fromRGB(255, 0, 0)
local GUESS_COLOR = Color3.fromRGB(0, 170, 255)

local OFF_COLOR   = Color3.fromRGB(60, 60, 60)
local FLAG_COLOR  = Color3.fromRGB(255, 165, 0)

-- One entry per highlight kind, so adding a kind never means editing render code.
local HIGHLIGHT_STYLE = {
    safe  = { color = SAFE_COLOR,  thickness = 0.08 },
    mine  = { color = MINE_COLOR,  thickness = 0.08 },
    guess = { color = GUESS_COLOR, thickness = 0.05 },
}

local GUESS_TIE_EPS = 1e-4  -- Scores within this of the best are not an improvement

----------------------------------------------------------------
-- HELPERS
----------------------------------------------------------------

local function clusterSorted(list, eps)
    local out = {}
    if #list == 0 then return out end
    local c, cnt = list[1], 1
    for i = 2, #list do
        local v = list[i]
        if math.abs(v - c) <= eps then
            cnt += 1
            c = c + (v - c) / cnt
        else
            out[#out+1] = c
            c, cnt = v, 1
        end
    end
    out[#out+1] = c
    return out
end

local function median(t)
    local n = #t
    if n == 0 then return nil end
    table.sort(t)
    return t[math.floor((n + 1) / 2)]
end

local function typicalSpacing(list)
    if #list < 2 then return 4 end
    local diffs = {}
    for i = 2, #list do diffs[i-1] = math.abs(list[i] - list[i-1]) end
    return median(diffs) or 4
end

local function nearestIndex(v, centers)
    local bestI, bestD = 1, math.huge
    for i = 1, #centers do
        local d = math.abs(v - centers[i])
        if d < bestD then bestD = d; bestI = i end
    end
    return bestI - 1
end

-- Flag check. Two flavours share one helper:
--   * Cached  (isFlaggedCached)  — reads cell.flagModel, refreshed only during the
--     periodic flagged-recheck. Used in the every-tick frontier scan (the hot path)
--     so we do one tree search per cell instead of one per tick.
--   * Fresh   (isFlaggedFresh)   — always re-searches. Used in the small action
--     loops (auto-flag / auto-reveal) where a stale flag could double-flag or stomp
--     a tile a player just flagged.
local function findFlagModel(part)
    return part:FindFirstChildOfClass("Model")
end

local function isFlaggedCached(cell)
    local f = cell.flagModel
    if f == nil then
        f = findFlagModel(cell.part)
        cell.flagModel = f
    end
    return f ~= nil
end

local function isFlaggedFresh(cell)
    cell.flagModel = findFlagModel(cell.part)
    return cell.flagModel ~= nil
end

-- `state` is the single source of truth for coveredness: detectState only ever
-- leaves "unknown" on a cell that is still covered and unflagged.
local function isCoveredCell(cell)
    return cell.state == "unknown"
end

-- Reverse adjacency (neighbour -> numbered cells referencing it). Built lazily by
-- planMove and reset here because it is invalidated only by a geometry rebuild.
local _revAdj = {}
local _revAdjCount = 0

----------------------------------------------------------------
-- OUTLINE SYSTEM (GPU SELECTIONBOX UPGRADE)
----------------------------------------------------------------

local function hideBorders(cell)
    if cell.selectionBox then
        cell.selectionBox.Visible = false
    end
    cell.highlight = nil
end

local function showBorders(cell, color, thickness)
    if not cell.selectionBox then
        local box = Instance.new("SelectionBox")
        box.SurfaceTransparency = 1
        box.Adornee = cell.part
        box.Parent = cell.part
        cell.selectionBox = box
    end
    
    cell.selectionBox.LineThickness = thickness or 0.05
    cell.selectionBox.Color3 = color
    cell.selectionBox.Visible = true
end

-- Apply a highlight kind ("safe"/"mine"/"guess") to a cell, or clear it when nil.
local function setHighlight(cell, want)
    if want == cell.highlight then return end
    if want == nil then
        hideBorders(cell)
        return
    end
    cell.highlight = want
    local style = HIGHLIGHT_STYLE[want]
    showBorders(cell, style.color, style.thickness)
end

local function destroyAllBorders()
    for ix = 0, data.grid.w - 1 do
        local row = data.cells.grid[ix]
        if row then
            for iz = 0, data.grid.h - 1 do
                local cell = row[iz]
                if cell and cell.selectionBox then
                    cell.selectionBox:Destroy()
                    cell.selectionBox = nil
                    cell.highlight = nil
                end
            end
        end
    end
end

----------------------------------------------------------------
-- GRID GEOMETRY
----------------------------------------------------------------

local function buildGridGeometry(partsFolder)
    destroyAllBorders()
    _revAdj, _revAdjCount = {}, 0
    data.cells.grid = {}
    data.grid.w, data.grid.h = 0, 0

    local parts = partsFolder:GetChildren()
    if #parts == 0 then return end

    local raw = {}
    local xs, zs = {}, {}
    local sumY = 0

    for _, part in ipairs(parts) do
        local pos = part.Position
        raw[#raw+1] = { part = part, pos = pos }
        xs[#xs+1] = pos.X
        zs[#zs+1] = pos.Z
        sumY += pos.Y
    end

    table.sort(xs); table.sort(zs)
    xs = clusterSorted(xs, typicalSpacing(xs) * 0.6)
    zs = clusterSorted(zs, typicalSpacing(zs) * 0.6)

    data.grid.w = #xs
    data.grid.h = #zs
    -- Kept for pos -> cell lookups (the follow pathfinder needs them).
    data.grid.xs, data.grid.zs = xs, zs
    data.grid.sx = typicalSpacing(xs)
    data.grid.sz = typicalSpacing(zs)
    if data.grid.w == 0 or data.grid.h == 0 then return end

    local planeY = sumY / #parts

    for iz = 0, data.grid.h - 1 do
        for ix = 0, data.grid.w - 1 do
            local row = data.cells.grid[ix]
            if not row then row = {}; data.cells.grid[ix] = row end
            row[iz] = {
                ix = ix, iz = iz,
                pos = Vector3.new(xs[ix+1], planeY, zs[iz+1]),
                part = nil, state = "unknown", number = nil,
                highlight = nil, cachedGui = nil, flagModel = nil
            }
        end
    end

    for _, r in ipairs(raw) do
        local ix = nearestIndex(r.pos.X, xs)
        local iz = nearestIndex(r.pos.Z, zs)
        local cell = data.cells.grid[ix][iz]
        if not cell.part then
            cell.part = r.part
            cell.pos  = r.pos
        else
            -- Squared distance: only the ordering matters, so skip the sqrt.
            local cx, cz = xs[ix+1], zs[iz+1]
            local op = cell.part.Position
            local od = (op.X - cx)^2 + (op.Z - cz)^2
            local nd = (r.pos.X - cx)^2 + (r.pos.Z - cz)^2
            if nd < od then cell.part = r.part; cell.pos = r.pos end
        end
    end

    for iz = 0, data.grid.h - 1 do
        for ix = 0, data.grid.w - 1 do
            local c = data.cells.grid[ix][iz]
            local neigh = {}
            for dz = -1, 1 do
                for dx = -1, 1 do
                    if dx ~= 0 or dz ~= 0 then
                        local jx, jz = ix+dx, iz+dz
                        if jx >= 0 and jx < data.grid.w and jz >= 0 and jz < data.grid.h then
                            neigh[#neigh+1] = data.cells.grid[jx][jz]
                        end
                    end
                end
            end
            c.neigh = neigh
        end
    end

    -- (Re)seed the incremental cell lists: every real tile starts unknown+covered.
    -- Terminal number/revealed cells and flags are discovered by refreshCellStates
    -- on the following tick(s); only cells with a part enter the active frontier.
    data.cells.numbered = {}
    data.cells.covered  = {}
    data.cells.flagged  = {}
    data.cells.toFlag   = {}
    data.cells.toClear  = {}
    data.lastBorderPos  = nil
    for iz = 0, data.grid.h - 1 do
        for ix = 0, data.grid.w - 1 do
            local c = data.cells.grid[ix][iz]
            if c.part then
                c.state     = "unknown"
                c.number    = nil
                c.highlight = nil
                c.cachedGui = nil
                c.flagModel = nil
                c._dirty    = nil
                data.cells.covered[#data.cells.covered+1] = c
            end
        end
    end
end

----------------------------------------------------------------
-- STATE REFRESH (CACHED EDITION)
----------------------------------------------------------------

-- Classify a single cell by reading its part/GUI. Mutates cell.state/number.
-- Returns "flagged" | "number" | "revealed_blank" | "covered" (covered == still
-- unknown+covered), or nil when the cell has no part.
local function detectState(cell)
    local part = cell.part
    if not part then return nil end

    cell.number = nil
    local covered = true

    if not cell.cachedGui then
        cell.cachedGui = part:FindFirstChild("NumberGui")
    end
    if cell.cachedGui then
        local tl = cell.cachedGui:FindFirstChild("TextLabel")
        if tl and tonumber(tl.Text) then
            cell.number = tonumber(tl.Text)
            covered = false
        end
    end

    if covered then
        local col = part.Color
        if col.R > 0.99 and col.G > 0.99 and col.B > 0.48 and col.B < 0.50 then
            covered = false
        end
    end

    if isFlaggedCached(cell) then
        cell.state = "flagged"
        return "flagged"
    elseif cell.number and not covered then
        cell.state = "number"
        if cell.highlight ~= nil then hideBorders(cell) end
        return "number"
    elseif not covered then
        cell.state = "revealed_blank"
        if cell.highlight ~= nil then hideBorders(cell) end
        return "revealed_blank"
    else
        cell.state = "unknown"
        return "covered"
    end
end

-- Incremental refresh: scans only cells that can still change (the unknown+covered
-- frontier), plus a periodic recheck of flagged cells. Terminal number/revealed
-- cells stay in persistent lists and are never rescanned. Returns true if any
-- cell transitioned state this tick.
local function refreshCellStates()
    if data.grid.w == 0 then return false end

    data.tickCounter += 1
    local recheckFlags = (data.tickCounter % Settings.FlagRecheckEvery) == 0
    local changed = false
    local covered = data.cells.covered

    -- Scan the unknown+covered frontier; swap-remove anything that transitions out.
    local i, n = 1, #covered
    while i <= n do
        local cell   = covered[i]
        local result = detectState(cell)
        if result == nil or result ~= "covered" then
            covered[i] = covered[n]
            covered[n] = nil
            n -= 1
            if result == "flagged" then
                data.cells.flagged[#data.cells.flagged+1] = cell
                changed = true
            elseif result == "number" then
                data.cells.numbered[#data.cells.numbered+1] = cell
                changed = true
            elseif result == "revealed_blank" then
                changed = true
            end
            -- result == nil (no part): silently dropped from the frontier
        else
            i += 1
        end
    end

    -- Periodically recheck flagged cells: a flag can be removed, revealing the tile.
    if recheckFlags then
        local flagged = data.cells.flagged
        local stillFlagged = {}
        for idx = 1, #flagged do
            local cell = flagged[idx]
            local part = cell.part
            cell.flagModel = nil -- force a fresh tree search this pass
            if part and findFlagModel(part) then
                stillFlagged[#stillFlagged+1] = cell
            else
                local result = detectState(cell)
                changed = true
                if result == "covered" then
                    covered[#covered+1] = cell
                elseif result == "number" then
                    data.cells.numbered[#data.cells.numbered+1] = cell
                end
                -- revealed_blank or nil: leaves the active sets entirely
            end
        end
        data.cells.flagged = stillFlagged
    end

    return changed
end

----------------------------------------------------------------
-- SOLVER (ADVANCED PROOF BY CONTRADICTION)
----------------------------------------------------------------

local _planCons = {}
local _assumeFlags = {}   -- reused by testContradiction to avoid per-call table churn
local _assumeClears = {}

local function planMove()
    if data.grid.w == 0 or #data.cells.numbered == 0 then
        data.cells.toFlag  = {}
        data.cells.toClear = {}
        data.toFlagCount   = 0
        data.toClearCount  = 0
        return
    end

    local knownFlag, knownClear = {}, {}

    -- Seed known flags from the persistent flagged list (no full-grid scan).
    for _, c in ipairs(data.cells.flagged) do knownFlag[c] = true end

    local numbered = data.cells.numbered

    -- Reverse adjacency: which numbered cells reference each neighbour. Both the
    -- neighbour structure and the numbered list are append-only until the next
    -- geometry rebuild, so extend the cache instead of rebuilding it every call.
    local revAdj = _revAdj
    for i = _revAdjCount + 1, #numbered do
        local c = numbered[i]
        for _, nb in ipairs(c.neigh) do
            local r = revAdj[nb]
            if not r then r = {}; revAdj[nb] = r end
            r[#r+1] = c
        end
    end
    _revAdjCount = #numbered

    local function markDirty(u)
        local r = revAdj[u]
        if r then for _, c in ipairs(r) do c._dirty = true end end
    end

    -- Memoized constraint: recomputed only when one of its neighbours gains a new
    -- flag/clear (signalled via markDirty). Otherwise the cached unknowns/remaining/
    -- set is reused across phases and guard-loop iterations.
    local function getConstraint(c)
        if not c._dirty then return c._cu, c._cr end
        c._dirty = false
        local unknowns, set, flagged = {}, {}, 0
        for _, nb in ipairs(c.neigh) do
            if knownFlag[nb] or nb.state == "flagged" then
                flagged += 1
            elseif not knownClear[nb] and isCoveredCell(nb) then
                unknowns[#unknowns+1] = nb
                set[nb] = true
            end
        end
        c._cu = unknowns
        c._cs = set
        c._cr = (c.number or 0) - flagged
        return unknowns, c._cr
    end

    -- Invalidate every constraint once at the start of the call.
    for _, c in ipairs(numbered) do c._dirty = true end

    local changed  = true
    local guard    = 0

    while changed and guard < Settings.PlanGuardLimit do
        changed = false
        guard  += 1

        -- 1. TRIVIAL LOGIC
        for _, c in ipairs(numbered) do
            local unknowns, rem = getConstraint(c)
            if rem > 0 and rem == #unknowns then
                for _, u in ipairs(unknowns) do
                    if not knownFlag[u] then knownFlag[u] = true; changed = true; markDirty(u) end
                end
            elseif rem == 0 and #unknowns > 0 then
                for _, u in ipairs(unknowns) do
                    if not knownClear[u] then knownClear[u] = true; changed = true; markDirty(u) end
                end
            end
        end

        -- 2. SUBSET LOGIC (spatially bucketed — was O(K^2), now ~O(K * local density))
        local cons = _planCons
        table.clear(cons)
        for _, c in ipairs(numbered) do
            local u = getConstraint(c)
            if #u > 0 then cons[#cons+1] = c end
        end

        if #cons > 0 then
            -- Bucket by floor(ix/3), floor(iz/3). Two constraints can only interact
            -- when |dix|<=2 and |diz|<=2, i.e. bucket diff <= 1 on each axis; the
            -- remaining pairs are skipped without ever being compared.
            local buckets = {}
            for idx = 1, #cons do
                local c  = cons[idx]
                local bx = math.floor(c.ix / 3)
                local bz = math.floor(c.iz / 3)
                local col = buckets[bx]
                if not col then col = {}; buckets[bx] = col end
                local b = col[bz]
                if not b then b = {}; col[bz] = b end
                b[#b+1] = idx
            end

            for i = 1, #cons do
                local a   = cons[i]
                local aU  = a._cu
                local aS  = a._cs
                local aR  = a._cr
                local abx = math.floor(a.ix / 3)
                local abz = math.floor(a.iz / 3)

                for dbx = -1, 1 do
                    local col = buckets[abx + dbx]
                    if col then
                        for dbz = -1, 1 do
                            local bkt = col[abz + dbz]
                            if bkt then
                                for _, j in ipairs(bkt) do
                                    if j ~= i then
                                        local b = cons[j]
                                        if b._cr >= aR
                                           and math.abs(a.ix - b.ix) <= 2
                                           and math.abs(a.iz - b.iz) <= 2 then
                                            -- is a (subset) of b?
                                            local allIn = true
                                            for _, u in ipairs(aU) do
                                                if not b._cs[u] then allIn = false; break end
                                            end
                                            if allIn then
                                                local diff = b._cr - aR
                                                -- only = b's unknowns not in a
                                                local only
                                                for _, u in ipairs(b._cu) do
                                                    if not aS[u] then
                                                        only = only or {}
                                                        only[#only+1] = u
                                                    end
                                                end
                                                if only and diff <= #only then
                                                    if diff == 0 then
                                                        for _, u in ipairs(only) do
                                                            if not knownClear[u] then knownClear[u] = true; changed = true; markDirty(u) end
                                                        end
                                                    elseif diff == #only then
                                                        for _, u in ipairs(only) do
                                                            if not knownFlag[u] then knownFlag[u] = true; changed = true; markDirty(u) end
                                                        end
                                                    end
                                                end
                                            end
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
            end
        end

        -- 3. PROOF BY CONTRADICTION (WITH CPU THERMAL CAP)
        if not changed then
            -- Merged validity check + frontier build (was two passes over `numbered`).
            local baseInvalid = false
            local frontier = {}
            local isFrontier = {}
            for _, c in ipairs(numbered) do
                local u, r = getConstraint(c)
                if r < 0 or r > #u then
                    baseInvalid = true
                    break
                end
                for _, unk in ipairs(u) do
                    if not isFrontier[unk] then
                        isFrontier[unk] = true
                        frontier[#frontier+1] = unk
                    end
                end
            end

            -- CPU cap for low-end devices: skip (and end the loop) if frontier is huge.
            if not baseInvalid and #frontier <= Settings.ContradictionCap then
                local function testContradiction(testCell, assumeMine)
                    table.clear(_assumeFlags)
                    table.clear(_assumeClears)
                    if assumeMine then
                        _assumeFlags[testCell] = true
                    else
                        _assumeClears[testCell] = true
                    end

                    local localChanged = true
                    local localLoops = 0

                    while localChanged and localLoops < Settings.ContradictionLoops do
                        localChanged = false
                        localLoops += 1

                        for _, c in ipairs(numbered) do
                            local unk, flagged = 0, 0
                            for _, nb in ipairs(c.neigh) do
                                if knownFlag[nb] or nb.state == "flagged" or _assumeFlags[nb] then
                                    flagged += 1
                                elseif not knownClear[nb] and isCoveredCell(nb) and not _assumeClears[nb] then
                                    unk += 1
                                end
                            end

                            local rem = (c.number or 0) - flagged
                            if rem < 0 or rem > unk then return true end

                            if rem > 0 and rem == unk then
                                for _, nb in ipairs(c.neigh) do
                                    if not knownClear[nb] and isCoveredCell(nb) and not _assumeClears[nb] and not _assumeFlags[nb] then
                                        _assumeFlags[nb] = true
                                        localChanged = true
                                    end
                                end
                            elseif rem == 0 and unk > 0 then
                                for _, nb in ipairs(c.neigh) do
                                    if not knownClear[nb] and isCoveredCell(nb) and not _assumeClears[nb] and not _assumeFlags[nb] then
                                        _assumeClears[nb] = true
                                        localChanged = true
                                    end
                                end
                            end
                        end
                    end
                    return false
                end

                for _, fCell in ipairs(frontier) do
                    if testContradiction(fCell, true) then
                        if not knownClear[fCell] then knownClear[fCell] = true; changed = true; markDirty(fCell) end
                    elseif testContradiction(fCell, false) then
                        if not knownFlag[fCell] then knownFlag[fCell] = true; changed = true; markDirty(fCell) end
                    end
                end
            end
        end
    end

    local toFlag, toClear = {}, {}
    local nFlag, nClear = 0, 0
    for c in pairs(knownFlag)  do toFlag[c]  = true; nFlag  += 1 end
    for c in pairs(knownClear) do toClear[c] = true; nClear += 1 end
    data.cells.toFlag  = toFlag
    data.cells.toClear = toClear
    data.toFlagCount   = nFlag
    data.toClearCount  = nClear
end

----------------------------------------------------------------
-- GUESS HELPER
----------------------------------------------------------------

local function computeBestGuess()
    data.bestGuessCell  = nil
    data.bestGuessScore = nil

    if not Settings.GuessHelper then return end
    if next(data.cells.toClear) ~= nil then return end
    if data.grid.w == 0 then return end

    local bestCell, bestScore = nil, nil
    local blindCell, blindScore = nil, nil
    local toFlag = data.cells.toFlag
    local blind = Settings.GuessDensityPrior

    -- Derive (remaining mines, unknown neighbours) once per numbered cell. Doing it
    -- inside the covered loop instead re-scanned each constraint up to 8 times.
    local remOf, unkOf = {}, {}
    for _, nb in ipairs(data.cells.numbered) do
        if nb.number and nb.number > 0 then
            local flagged, unk = 0, 0
            for _, n2 in ipairs(nb.neigh) do
                if n2.state == "flagged" or toFlag[n2] then
                    flagged += 1
                elseif isCoveredCell(n2) then
                    unk += 1
                end
            end
            remOf[nb] = nb.number - flagged
            unkOf[nb] = unk
        end
    end

    -- data.cells.covered only holds unknown+unflagged cells, so no instance lookup
    -- is needed to rule flagged tiles out here.
    for _, cell in ipairs(data.cells.covered) do
        if not cell.part then continue end
        if toFlag[cell] then continue end

        local riskSum, contribs = 0, 0
        for _, nb in ipairs(cell.neigh) do
            local rem = remOf[nb]
            if rem then
                local unk = unkOf[nb]
                if rem <= 0 then
                    contribs += 1
                elseif unk > 0 then
                    riskSum += rem / unk
                    contribs += 1
                end
            end
        end

        if contribs > 0 then
            local score = riskSum / contribs
            if not bestScore or score < bestScore - GUESS_TIE_EPS then
                bestScore = score
                bestCell  = cell
            end
        elseif blind > 0 then
            -- No adjacent number constrains this cell: it is a pure blind guess.
            -- Prefer cells on the frontier edges (fewer neighbours => a mine there
            -- also threatens fewer numbers) as a cheap spatial tie-break.
            local score = blind * (1 + #cell.neigh * 0.01)
            if not blindScore or score < blindScore - GUESS_TIE_EPS then
                blindScore = score
                blindCell  = cell
            end
        end
    end

    -- Constraint-informed guesses are strictly better than blind ones.
    if bestCell then
        data.bestGuessCell  = bestCell
        data.bestGuessScore = bestScore
    elseif blindCell then
        data.bestGuessCell  = blindCell
        data.bestGuessScore = blindScore
    end
end

----------------------------------------------------------------
-- AUTO-FLAG
----------------------------------------------------------------

local _autoFlagWarnedOnce = false
local _lastAutoFlagTime   = 0

local function autoFlagCell(cell, hrpPos)
    if tick() - _lastAutoFlagTime < Settings.AutoFlagCooldown then return end
    if not cell.part or isFlaggedFresh(cell) then return end
    if hrpPos and (cell.pos - hrpPos).Magnitude > Settings.AutoFlagRange then return end

    local cd = cell.part:FindFirstChildOfClass("ClickDetector")
    if not cd then
        if not _autoFlagWarnedOnce then
            _autoFlagWarnedOnce = true
            warn("[MinesweeperSolver] AutoFlag disabled: no ClickDetector on tiles.")
        end
        return
    end

    local ok, err = pcall(fireclickdetector, cd)
    if ok then
        _lastAutoFlagTime = tick()
    else
        warn("[MinesweeperSolver] fireclickdetector:", err)
    end
end

----------------------------------------------------------------
-- AUTO-REVEAL (THE MICRO-STOMP FIX)
----------------------------------------------------------------

local _autoRevealActive = false

-- Teleport just above a tile and slam down through it. Physics must stay active
-- (never anchor the root part) or the collision that reveals the tile never fires.
local function stompCell(hrp, cell)
    local part = cell.part
    local surfaceY = part.Position.Y + (part.Size.Y / 2) + Settings.RevealHoverHeight
    hrp.CFrame = CFrame.new(part.Position.X, surfaceY, part.Position.Z)
    hrp.AssemblyLinearVelocity = Vector3.new(0, Settings.StompVelocity, 0)
    task.wait(Settings.AutoRevealDelay)
    hrp.AssemblyLinearVelocity = Vector3.zero
end

local function autoRevealNext()
    if not Settings.AutoReveal then return end
    if _autoRevealActive then return end

    local player = Players.LocalPlayer
    if not player or not player.Character then return end
    local hrp = player.Character:FindFirstChild("HumanoidRootPart")
    local humanoid = player.Character:FindFirstChildOfClass("Humanoid")
    if not hrp or not humanoid then return end

    _autoRevealActive = true

    task.spawn(function()
        -- Build a distance-ordered list (nearest first) so we walk a short path
        -- instead of teleporting around the board in hash order.
        local ordered = {}
        local count = 0
        local hrpPos = hrp.Position
        for cell in pairs(data.cells.toClear) do
            if cell.part and isCoveredCell(cell) and not isFlaggedFresh(cell) then
                count += 1
                local dx = cell.pos.X - hrpPos.X
                local dz = cell.pos.Z - hrpPos.Z
                ordered[count] = { cell = cell, d = dx*dx + dz*dz }
            end
        end
        local best = data.bestGuessCell
        if best and best.part and isCoveredCell(best) and not isFlaggedFresh(best) then
            local dx = best.pos.X - hrpPos.X
            local dz = best.pos.Z - hrpPos.Z
            ordered[count+1] = { cell = best, d = dx*dx + dz*dz }
        end
        table.sort(ordered, function(a, b) return a.d < b.d end)

        for _, e in ipairs(ordered) do
            if _stopped or not Settings.AutoReveal then break end
            if e.cell.part and isCoveredCell(e.cell) and not isFlaggedFresh(e.cell) then
                stompCell(hrp, e.cell)
            end
        end

        humanoid:ChangeState(Enum.HumanoidStateType.GettingUp)
        _autoRevealActive = false
    end)
end

----------------------------------------------------------------
-- BORDER RENDERING
----------------------------------------------------------------

local _candCells = {}
local _candWant  = {}
local _candDist  = {}
local _candIdx   = {}

-- Hoisted so the sort does not allocate a fresh closure on every redraw.
local function _byCandDist(a, b)
    return _candDist[a] < _candDist[b]
end

-- Auto-flag is decoupled from rendering: it runs every tick (the per-cell cooldown,
-- range and ClickDetector checks live inside autoFlagCell) so flagging retries
-- survive the border-redraw throttle below.
local function runAutoFlag(hrpPos)
    if not Settings.AutoFlag then return end
    for cell in pairs(data.cells.toFlag) do
        autoFlagCell(cell, hrpPos)
    end
end

local function updateBorders(hrpPos)
    if data.grid.w == 0 then return end

    local bestGuessCell = data.bestGuessCell
    if not hrpPos then
        local char = Players.LocalPlayer and Players.LocalPlayer.Character
        local hrp  = char and char:FindFirstChild("HumanoidRootPart")
        if hrp then hrpPos = hrp.Position end
    end

    local toFlag, toClear = data.cells.toFlag, data.cells.toClear
    local maxHL   = Settings.MaxVisibleHL
    local rangeSq = Settings.HighlightRange * Settings.HighlightRange

    -- Gather candidates into flat, reused arrays (no per-entry table allocation).
    local cN = 0
    for _, cell in ipairs(data.cells.covered) do
        local part = cell.part
        if part then
            local wantHL = nil
            if toFlag[cell] then
                wantHL = "mine"
            elseif toClear[cell] then
                wantHL = "safe"
            elseif cell == bestGuessCell then
                wantHL = "guess"
            end

            if wantHL == nil then
                -- Cell no longer needs a highlight — clear if it had one
                if cell.highlight ~= nil then hideBorders(cell) end
            else
                local distSq = 0
                if hrpPos then
                    local dx = cell.pos.X - hrpPos.X
                    local dz = cell.pos.Z - hrpPos.Z
                    distSq = dx*dx + dz*dz
                end
                if distSq <= rangeSq then
                    cN += 1
                    _candCells[cN] = cell
                    _candWant[cN]  = wantHL
                    _candDist[cN]  = distSq
                else
                    -- Out of range: hide
                    if cell.highlight ~= nil then hideBorders(cell) end
                end
            end
        end
    end
    -- Trim stale tails left over from a larger previous call.
    for k = cN + 1, #_candCells do
        _candCells[k] = nil
        _candWant[k]  = nil
        _candDist[k]  = nil
    end

    -- Index-sort by distance (render only the closest maxHL, hide the rest).
    local idx = _candIdx
    table.clear(idx)
    for k = 1, cN do idx[k] = k end
    table.sort(idx, _byCandDist)

    local limit = math.min(cN, maxHL)
    for rank = 1, cN do
        local entry = idx[rank]
        local cell  = _candCells[entry]
        if rank <= limit then
            setHighlight(cell, _candWant[entry])
        else
            -- Over cap: hide if it previously had a highlight
            if cell.highlight ~= nil then hideBorders(cell) end
        end
    end
end

----------------------------------------------------------------
-- DUMBASS MODE (WALK-FOLLOW A PLAYER)
----------------------------------------------------------------

-- Grid cell under a world position, or nil when the position is off the board.
local function cellIndexAt(pos)
    local g = data.grid
    if g.w == 0 or not g.xs then return nil end
    local ix = nearestIndex(pos.X, g.xs)
    local iz = nearestIndex(pos.Z, g.zs)
    if math.abs(pos.X - g.xs[ix+1]) > g.sx * 0.75 then return nil end
    if math.abs(pos.Z - g.zs[iz+1]) > g.sz * 0.75 then return nil end
    return ix, iz
end

-- Standing on a cell is only safe once it is revealed, or once the solver has
-- proven it clear. Unknown tiles are exactly what we refuse to walk over.
local function isWalkableCell(cell)
    if not cell then return false end
    return cell.state == "number" or cell.state == "revealed_blank"
        or data.cells.toClear[cell] ~= nil
end

local _bfsFrom = {}   -- reused between ticks; cleared on each search
local _bfsDirs = { {1,0}, {-1,0}, {0,1}, {0,-1} }

-- 4-neighbour BFS across walkable cells. Returns the first step to take toward
-- the goal cell, or nil when no safe route exists.
local function nextSafeStep(sx, sz, gx, gz)
    if sx == gx and sz == gz then return nil end
    table.clear(_bfsFrom)
    local grid, w, h = data.cells.grid, data.grid.w, data.grid.h
    local queue, head = { sx * h + sz }, 1
    _bfsFrom[sx * h + sz] = -1
    local goalKey = gx * h + gz
    while head <= #queue do
        local key = queue[head]; head += 1
        local cx, cz = key // h, key % h
        if key == goalKey then
            -- Walk the parent chain back to the cell right after the start.
            while _bfsFrom[key] ~= -1 and _bfsFrom[_bfsFrom[key]] ~= -1 do
                key = _bfsFrom[key]
            end
            return grid[key // h][key % h]
        end
        for _, d in ipairs(_bfsDirs) do
            local nx, nz = cx + d[1], cz + d[2]
            if nx >= 0 and nx < w and nz >= 0 and nz < h then
                local nkey = nx * h + nz
                if not _bfsFrom[nkey] then
                    local cell = grid[nx][nz]
                    -- The goal cell itself is allowed even if unrevealed: it is
                    -- where the target is standing, so it is safe by proof.
                    if nkey == goalKey or isWalkableCell(cell) then
                        _bfsFrom[nkey] = key
                        queue[#queue+1] = nkey
                    end
                end
            end
        end
    end
    return nil
end

-- Humanoid:MoveTo is re-issued every tick: it is a one-shot goal and the
-- target keeps moving. No CFrame writes, so this is plain walking.
local function runFollow()
    if not (Settings.DumbassMode and Settings.FollowTarget) then return end

    local target = Players:FindFirstChild(Settings.FollowTarget)
    local tHrp = target and target.Character and target.Character:FindFirstChild("HumanoidRootPart")
    if not tHrp then return end

    local char = Players.LocalPlayer and Players.LocalPlayer.Character
    local hum  = char and char:FindFirstChildOfClass("Humanoid")
    local hrp  = char and char:FindFirstChild("HumanoidRootPart")
    if not (hum and hrp) then return end

    local delta = tHrp.Position - hrp.Position
    if delta.Magnitude <= Settings.FollowDistance then
        hum:MoveTo(hrp.Position)
        data.followBlocked = false
        return
    end

    local sx, sz = cellIndexAt(hrp.Position)
    local gx, gz = cellIndexAt(tHrp.Position)
    if sx and gx then
        -- Both on the board: only step on tiles known not to be mines.
        local step = nextSafeStep(sx, sz, gx, gz)
        data.followBlocked = step == nil
        hum:MoveTo(step and step.pos or hrp.Position)
        return
    end

    data.followBlocked = false
    -- Aim short of the target so we don't shove them around.
    hum:MoveTo(tHrp.Position - delta.Unit * Settings.FollowDistance)
end

----------------------------------------------------------------
-- STATUS HUD (WITH LIVE SLIDER)
----------------------------------------------------------------

-- Paint a toggle button to match the setting it controls. Shared by creation and
-- by the per-frame HUD refresh so the two can never disagree.
local function syncToggleButton(btn, label, enabled, colorOn)
    btn.Text = label .. (enabled and ": ON" or ": OFF")
    btn.BackgroundColor3 = enabled and colorOn or OFF_COLOR
end

local function createToggleButton(gui, xOffset, label, colorOn, settingKey)
    local btn = Instance.new("TextButton")
    btn.Size            = UDim2.new(0, 150, 0, 36)
    btn.Position        = UDim2.new(1, xOffset, 0, 122)
    btn.BorderSizePixel = 0
    btn.Font            = Enum.Font.GothamBold
    btn.TextSize        = 13
    btn.TextColor3      = Color3.new(1, 1, 1)
    btn.AutoButtonColor = false
    btn.Parent          = gui
    syncToggleButton(btn, label, Settings[settingKey], colorOn)

    local corner = Instance.new("UICorner")
    corner.CornerRadius = UDim.new(0, 6)
    corner.Parent = btn

    btn.MouseButton1Click:Connect(function()
        Settings[settingKey] = not Settings[settingKey]
    end)
    return btn
end

-- Dropdown listing every other player; picking one sets Settings.FollowTarget.
-- The list is rebuilt on open, so joins/leaves need no event plumbing.
local function createPlayerDropdown(gui, xOffset)
    local btn = Instance.new("TextButton")
    btn.Size            = UDim2.new(0, 150, 0, 36)
    btn.Position        = UDim2.new(1, xOffset, 0, 122)
    btn.BorderSizePixel = 0
    btn.Font            = Enum.Font.GothamBold
    btn.TextSize        = 12
    btn.TextColor3      = Color3.new(1, 1, 1)
    btn.AutoButtonColor = false
    btn.BackgroundColor3 = OFF_COLOR
    btn.Text            = "Dumbass Mode: OFF"
    btn.Parent          = gui
    local c = Instance.new("UICorner"); c.CornerRadius = UDim.new(0, 6); c.Parent = btn

    local list = Instance.new("ScrollingFrame")
    list.Size             = UDim2.new(0, 150, 0, 140)
    list.Position         = UDim2.new(1, xOffset, 0, 160)
    list.BackgroundColor3 = Color3.fromRGB(25, 25, 25)
    list.BorderSizePixel  = 0
    list.ScrollBarThickness = 4
    list.Visible          = false
    list.Parent           = gui
    local lc = Instance.new("UICorner"); lc.CornerRadius = UDim.new(0, 6); lc.Parent = list
    local layout = Instance.new("UIListLayout"); layout.Parent = list

    local function addRow(text, onClick)
        local row = Instance.new("TextButton")
        row.Size            = UDim2.new(1, 0, 0, 24)
        row.BackgroundTransparency = 1
        row.Font            = Enum.Font.Gotham
        row.TextSize        = 12
        row.TextColor3      = Color3.new(1, 1, 1)
        row.Text            = text
        row.Parent          = list
        row.MouseButton1Click:Connect(onClick)
    end

    local function rebuild()
        for _, child in ipairs(list:GetChildren()) do
            if child:IsA("TextButton") then child:Destroy() end
        end
        addRow("(none - off)", function()
            Settings.FollowTarget = nil
            Settings.DumbassMode  = false
            list.Visible = false
        end)
        local n = 1
        for _, p in ipairs(Players:GetPlayers()) do
            if p ~= Players.LocalPlayer then
                n += 1
                addRow(p.Name, function()
                    Settings.FollowTarget = p.Name
                    Settings.DumbassMode  = true
                    list.Visible = false
                end)
            end
        end
        list.CanvasSize = UDim2.new(0, 0, 0, n * 24)
    end

    btn.MouseButton1Click:Connect(function()
        list.Visible = not list.Visible
        if list.Visible then rebuild() end
    end)
    return btn
end

-- Build a labelled drag slider bound to one numeric Setting. `opts.format` renders
-- the label, `opts.quantise` (optional) snaps the raw value before it is stored.
local function createSlider(gui, opts)
    local label = Instance.new("TextLabel")
    label.BackgroundTransparency = 1
    label.Position   = UDim2.new(1, -380, 0, opts.y)
    label.Size       = UDim2.new(0, 150, 0, 20)
    label.Font       = Enum.Font.GothamSemibold
    label.TextSize   = 12
    label.TextColor3 = Color3.new(0.8, 0.8, 0.8)
    label.Text       = string.format(opts.format, Settings[opts.settingKey])
    label.Parent     = gui

    local bar = Instance.new("TextButton")
    bar.BackgroundColor3 = Color3.fromRGB(40, 40, 40)
    bar.Position        = UDim2.new(1, -380, 0, opts.y + 20)
    bar.Size            = UDim2.new(0, 150, 0, 10)
    bar.Text            = ""
    bar.AutoButtonColor = false
    bar.Parent          = gui
    local barCorner = Instance.new("UICorner")
    barCorner.CornerRadius = UDim.new(1, 0)
    barCorner.Parent = bar

    local fill = Instance.new("Frame")
    fill.BackgroundColor3 = opts.color
    fill.Size     = UDim2.new(math.clamp(Settings[opts.settingKey] / opts.max, 0, 1), 0, 1, 0)
    fill.Position = UDim2.new(0, 0, 0, 0)
    fill.Parent   = bar
    local fillCorner = Instance.new("UICorner")
    fillCorner.CornerRadius = UDim.new(1, 0)
    fillCorner.Parent = fill

    local dragging = false

    local function update(input)
        local width = bar.AbsoluteSize.X
        if width <= 0 then return end
        local percent = math.clamp(input.Position.X - bar.AbsolutePosition.X, 0, width) / width
        local value = opts.max * percent
        if opts.quantise then value = opts.quantise(value) end
        Settings[opts.settingKey] = value
        fill.Size  = UDim2.new(percent, 0, 1, 0)
        label.Text = string.format(opts.format, value)
    end

    bar.InputBegan:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
            dragging = true
            update(input)
        end
    end)

    UserInputService.InputChanged:Connect(function(input)
        if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch) then
            update(input)
        end
    end)

    UserInputService.InputEnded:Connect(function(input)
        if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
            dragging = false
        end
    end)

    return label, fill
end

local function ensureStatusGui()
    if not Settings.GuiEnabled then return end
    if data.statusGui and data.statusLabel then return end

    local player = Players.LocalPlayer
    if not player then return end
    local pg = player:FindFirstChildOfClass("PlayerGui")
    if not pg then return end

    local gui = Instance.new("ScreenGui")
    gui.Name           = "MinesweeperSolverGui"
    gui.ResetOnSpawn   = false
    gui.IgnoreGuiInset = true
    gui.Parent         = pg

    local label = Instance.new("TextLabel")
    label.Name                  = "StatusLabel"
    label.BackgroundTransparency = 1
    label.Position              = UDim2.new(1, -540, 0, 10)
    label.Size                  = UDim2.new(0, 520, 0, 110)
    label.TextXAlignment        = Enum.TextXAlignment.Left
    label.TextYAlignment        = Enum.TextYAlignment.Top
    label.Font                  = Enum.Font.Code
    label.TextSize              = 14
    label.TextColor3            = Color3.new(1, 1, 1)
    label.RichText              = true
    label.Text                  = ""
    label.Parent                = gui

    data.statusGui   = gui
    data.statusLabel = label

    data.autoFlagBtn = createToggleButton(gui, -540, "AutoFlag", FLAG_COLOR, "AutoFlag")
    data.autoRevealBtn = createToggleButton(gui, -380, "AutoReveal", GUESS_COLOR, "AutoReveal")
    data.followBtn = createPlayerDropdown(gui, -220)

    data.sliderLabel, data.sliderFill = createSlider(gui, {
        y = 165, max = 0.20, color = GUESS_COLOR,
        settingKey = "AutoRevealDelay", format = "Reveal Delay: %.2fs",
    })

    data.rangeLabel, data.rangeFill = createSlider(gui, {
        y = 205, max = 100, color = FLAG_COLOR,
        settingKey = "AutoFlagRange", format = "AutoFlag Range: %d",
        quantise = function(v) return math.floor(v + 0.5) end,
    })
end

local function updateStatusGui()
    if not Settings.GuiEnabled or not data.statusLabel then return end

    local now = tick()
    if now - data.lastGuiUpdate < Settings.GuiUpdateInterval then return end
    data.lastGuiUpdate = now

    local mineCount, safeCount = data.toFlagCount, data.toClearCount

    local stateLine
    if next(data.cells.toClear) then
        stateLine = "State: <font color='#00FF00'>LOGIC</font> (safe moves available)"
    elseif data.bestGuessCell then
        stateLine = "State: <font color='#00AFFF'>GUESS</font> (no certain safe tiles)"
    else
        stateLine = "State: <font color='#FFAA00'>UNKNOWN</font> (no frontier info)"
    end

    local guessLine
    if data.bestGuessCell and data.bestGuessScore then
        local risk = math.clamp(data.bestGuessScore * 100, 0, 100)
        local risky = risk >= Settings.RiskWarnThreshold * 100
        local hex = risky and "#FF5555" or "#00AFFF"
        guessLine = string.format(
            "Best guess: ix=%d, iz=%d (<font color='#%s'>~%.1f%% mine risk%s</font>)",
            data.bestGuessCell.ix, data.bestGuessCell.iz, hex, risk,
            risky and " - RISKY" or ""
        )
    elseif Settings.GuessHelper then
        guessLine = "Best guess: none (logic available or no frontier)"
    else
        guessLine = "Best guess: disabled (press F8 to enable)"
    end

    local unknownCount = #data.cells.covered
    local estMines = math.floor(Settings.GuessDensityPrior * unknownCount)

    data.statusLabel.Text = string.format(
        "<b>Minesweeper Solver</b>\n"
        .. "Mode: <font color='#%s'>%s</font> | AutoFlag: <font color='#%s'>%s</font> | AutoReveal: <font color='#%s'>%s</font>\n"
        .. "Board: %dx%d | Numbered: %d | Unknown: %d\n"
        .. "Suggestions: %d mines, %d safe | Est. mines: ~%d\n"
        .. "%s\n%s\n"
        .. "[F6] Solver | [F7] AutoFlag | [F8] GuessHelper | [F9] AutoReveal",
        Settings.Enabled    and "00FF00" or "FF5555", Settings.Enabled    and "ON" or "OFF",
        Settings.AutoFlag   and "FFA500" or "888888", Settings.AutoFlag   and "ON" or "OFF",
        Settings.AutoReveal and "00AAFF" or "888888", Settings.AutoReveal and "ON" or "OFF",
        data.grid.w, data.grid.h, #data.cells.numbered, unknownCount,
        mineCount, safeCount, estMines,
        stateLine, guessLine
    )

    if data.autoFlagBtn then
        syncToggleButton(data.autoFlagBtn, "AutoFlag", Settings.AutoFlag, FLAG_COLOR)
    end

    if data.autoRevealBtn then
        syncToggleButton(data.autoRevealBtn, "AutoReveal", Settings.AutoReveal, GUESS_COLOR)
    end
    if data.followBtn then
        local on = Settings.DumbassMode and Settings.FollowTarget
        data.followBtn.Text = on
            and ((data.followBlocked and "Waiting: " or "Following: ") .. Settings.FollowTarget)
            or "Dumbass Mode: OFF"
        data.followBtn.BackgroundColor3 = on and SAFE_COLOR or OFF_COLOR
    end
end

----------------------------------------------------------------
-- INPUT
----------------------------------------------------------------

UserInputService.InputBegan:Connect(function(input, gp)
    if _stopped or gp then return end
    if input.KeyCode == Enum.KeyCode.F6 then
        Settings.Enabled = not Settings.Enabled
    elseif input.KeyCode == Enum.KeyCode.F7 then
        Settings.AutoFlag = not Settings.AutoFlag
    elseif input.KeyCode == Enum.KeyCode.F8 then
        Settings.GuessHelper = not Settings.GuessHelper
        if not Settings.GuessHelper then
            data.bestGuessCell  = nil
            data.bestGuessScore = nil
        end
    elseif input.KeyCode == Enum.KeyCode.F9 then
        Settings.AutoReveal = not Settings.AutoReveal
    end
end)

----------------------------------------------------------------
-- EVENT DRIVEN MAIN LOOP
----------------------------------------------------------------

-- Locate the folder of tile parts. Tries the configured path first, then, when
-- AutoDiscover is on, lazily scans the Workspace once for a Model whose child
-- folder holds a dense cluster of parts (a plausible grid). Result is cached.
local _discoverDone = false
local _discoveredFolder = nil
local function resolvePartsFolder()
    local root = workspace:FindFirstChild(Settings.BoardRootName)
    if root then
        local f = root:FindFirstChild(Settings.PartsFolderName)
        if f then return f end
    end
    if not Settings.AutoDiscover then return nil end
    if _discoverDone then return _discoveredFolder end
    _discoverDone = true

    for _, model in ipairs(workspace:GetChildren()) do
        if model:IsA("Model") then
            local f = model:FindFirstChild(Settings.PartsFolderName)
            if not f then
                for _, child in ipairs(model:GetChildren()) do
                    if child:IsA("Folder") then f = child break end
                end
            end
            if f then
                local n = 0
                for _, child in ipairs(f:GetChildren()) do
                    if child:IsA("BasePart") then
                        n += 1
                    else
                        n = 0
                        break
                    end
                end
                if n >= 9 then
                    _discoveredFolder = f
                    return f
                end
            end
        end
    end
    return nil
end

-- Decoupled solver loop: instead of running every Heartbeat (60Hz) and throttling,
-- we sleep between ticks. On low-end devices this alone can save 5-10% CPU. When
-- the board is fully idle (nothing to flag/clear/reveal) the sleep grows toward
-- IdleSleepCap, cutting CPU further until a change wakes it back up.
task.spawn(function()
    local lastGridCheck = 0
    local idleTicks = 0
    while not _stopped do
        local ok, err = pcall(function()
            local now = tick()

            -- Follow runs before every board early-return so it keeps working
            -- with the solver off or no grid loaded.
            runFollow()

            if now - lastGridCheck > Settings.GridCheckInterval then
                lastGridCheck = now
                local folder = resolvePartsFolder()
                if folder then
                    local count = #folder:GetChildren()
                    if count ~= data.lastPartCount then
                        data.lastPartCount = count
                        buildGridGeometry(folder)
                    end
                end
            end

            if data.grid.w == 0 or data.grid.h == 0 then
                idleTicks += 1
                return
            end

            local char   = Players.LocalPlayer and Players.LocalPlayer.Character
            local hrp    = char and char:FindFirstChild("HumanoidRootPart")
            local hrpPos = hrp and hrp.Position

            if not Settings.Enabled then
                data.cells.toFlag   = {}
                data.cells.toClear  = {}
                data.toFlagCount    = 0
                data.toClearCount   = 0
                data.bestGuessCell  = nil
                data.bestGuessScore = nil
                refreshCellStates() -- still needed so the covered frontier stays current
                updateBorders(hrpPos)
                ensureStatusGui()
                updateStatusGui()
                idleTicks += 1
                return
            end

            local boardChanged = refreshCellStates()
            if boardChanged then
                planMove()
                computeBestGuess()
                ensureStatusGui()
                updateStatusGui()
            end

            -- Auto-flag every tick: cooldown/range/ClickDetector are gated inside
            -- autoFlagCell, so this stays cheap and retries across cooldown boundaries.
            runAutoFlag(hrpPos)

            -- Border redraws react to board changes or player movement only. When
            -- neither has happened we skip the full covered scan entirely.
            local needBorders = boardChanged
            if not needBorders and hrpPos then
                local last = data.lastBorderPos
                if not last then
                    needBorders = true
                else
                    local dx = hrpPos.X - last.X
                    local dz = hrpPos.Z - last.Z
                    local threshold = Settings.BorderMoveThreshold
                    if dx*dx + dz*dz > threshold * threshold then needBorders = true end
                end
            end
            if needBorders then
                updateBorders(hrpPos)
                data.lastBorderPos = hrpPos
            elseif not hrpPos and data.lastBorderPos then
                data.lastBorderPos = nil
            end

            autoRevealNext()

            -- Idle detection: nothing left to act on this tick.
            if boardChanged or data.toFlagCount > 0 or data.toClearCount > 0
                or (Settings.AutoReveal and data.bestGuessCell ~= nil) then
                idleTicks = 0
            else
                idleTicks += 1
            end
        end)
        if not ok then warn("[MinesweeperSolver] tick error:", err) end

        -- Ramp the sleep toward IdleSleepCap the longer the board stays idle.
        local sleepT = Settings.SolverTickRate
        if idleTicks > Settings.IdleSleepAfter then
            local f = math.min((idleTicks - Settings.IdleSleepAfter) / 8, 1)
            sleepT = sleepT + (Settings.IdleSleepCap - sleepT) * f
        end
        task.wait(sleepT)
    end
end)

print("=== Minesweeper Solver Loaded ===")
