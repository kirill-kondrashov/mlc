-- The worked example uses short, unmerged tables. Keep each table together;
-- longtable splitting is unreliable with this installation of XeLaTeX.
function Table(tbl)
  if FORMAT ~= "latex" then return nil end
  local lines = {
    "\\begin{center}",
    "\\begin{tabular}{@{}" .. string.rep("l", #tbl.colspecs) .. "@{}}",
    "\\toprule"
  }
  local function append_rows(rows)
    for _, row in ipairs(rows) do
      local cells = {}
      for _, cell in ipairs(row.cells) do
        if cell.row_span ~= 1 or cell.col_span ~= 1 then
          error("The worked example requires unmerged table cells")
        end
        local value = pandoc.write(pandoc.Pandoc(cell.contents), "latex")
        cells[#cells + 1] = value:gsub("%s+$", "")
      end
      lines[#lines + 1] = table.concat(cells, " & ") .. " \\\\"
    end
  end
  append_rows(tbl.head.rows)
  if #tbl.head.rows > 0 then lines[#lines + 1] = "\\midrule" end
  for _, body in ipairs(tbl.bodies) do
    append_rows(body.head)
    append_rows(body.body)
  end
  append_rows(tbl.foot.rows)
  lines[#lines + 1] = "\\bottomrule"
  lines[#lines + 1] = "\\end{tabular}"
  lines[#lines + 1] = "\\end{center}"
  return pandoc.RawBlock("latex", table.concat(lines, "\n"))
end
