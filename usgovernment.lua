local urlparse = require("socket.url")
local http = require("socket.http")
local html_entities = require("htmlEntities")
local cjson = require("cjson")

local item_dir = os.getenv("item_dir")
local item_name = os.getenv("item_name")
local warc_file_base = os.getenv("warc_file_base")

local url_count = 0
local downloaded = {}
local abortgrab = false
local killgrab = false
local exit_url = false

local timestamp = nil

local current_file = nil
local current_file_html = nil
local current_file_url = nil

if urlparse == nil or http == nil or html_entities == nil then
  io.stdout:write("Dependencies not corrently installed.\n")
  io.stdout:flush()
  abortgrab = true
end

normalize_url = function(url)
  local candidate_current = url
  while true do
    local temp = string.lower(urlparse.unescape(candidate_current))
    if temp == candidate_current then
      break
    end
    candidate_current = temp
  end
  return candidate_current
end

local urls = {}
for url in string.gmatch(item_name, "([^\n]+)") do
  urls[normalize_url(url)] = true
end

local status_code = nil

local current_url = nil
local bad_urls = {}
local queued_urls = {}
local remove_params = {}
local paths = {}
local item_first_url = nil
local redirect_domains = {}
local redirect_urls = {}
local tlds = {}
local visited_urls = {}

local ftp_urls = {[""]={}}

local tlds_file = io.open("static-tlds.txt", "r")
for tld in tlds_file:lines() do
  tlds[tld] = true
end
tlds_file:close()

local remove_params_file = io.open("static-remove-params.txt", "r")
for param in remove_params_file:lines() do
  local param = string.gsub(
    param, "([a-zA-Z])",
    function(c)
      return "[" .. string.lower(c) .. string.upper(c) .. "]"
    end
  )
  table.insert(remove_params, param)
end
remove_params_file:close()

local paths_file = io.open("static-paths.txt", "r")
for line in paths_file:lines() do
  paths[line] = true
end
paths_file:close()

kill_grab = function(item)
  io.stdout:write("Aborting crawling.\n")
  killgrab = true
end

read_file = function(file, bytes)
  if not bytes then
    bytes = "*all"
  end
  if file then
    local f = assert(io.open(file))
    local data = f:read(bytes)
    f:close()
    if not data then
      data = ""
    end
    return data
  else
    return ""
  end
end

table_length = function(t)
  local count = 0
  if not t then
    return count
  end
  for _ in pairs(t) do
    count = count + 1
  end
  return count
end

bad_code = function(status_code)
  return status_code ~= 200
    and status_code ~= 301
    and status_code ~= 302
    and status_code ~= 303
    and status_code ~= 307
    and status_code ~= 308
    and status_code ~= 404
    and status_code ~= 410
end

find_path_loop = function(url, max_repetitions)
  local tested = {}
  local tempurl = urlparse.unescape(url)
  tempurl = string.match(tempurl, "^https?://[^/]+(.*)$")
  if not tempurl then
    return false
  end
  for s in string.gmatch(tempurl, "([^/%?&]+)") do
    s = string.lower(s)
    if not tested[s] then
      if s == "" then
        tested[s] = -2
      else
        tested[s] = 0
      end
    end
    tested[s] = tested[s] + 1
    if tested[s] == max_repetitions then
      return true
    end
  end
  return false
end

percent_encode_url = function(url)
  temp = ""
  for c in string.gmatch(url, "(.)") do
    local b = string.byte(c)
    if b < 32 or b > 126 then
      c = string.format("%%%02X", b)
    end
    temp = temp .. c
  end
  return temp
end

queue_url = function(url, withcustom)
  if not url then
    return nil
  end
  local origurl = url
  --[[if string.match(url, "^http://")
    and string.match(current_url, "^http://")
    and string.match(url, "^http://([^/]+)") ~= string.match(current_url, "^http://([^/]+)") then
    return nil
  end]]
  queue_new_urls(url)
  if not string.match(url, "^https?://[^/]+%.") then
    return nil
  end
  url = string.gsub(url, "'%s*%+%s*'", "")
  url = percent_encode_url(url)
  url = string.match(url, "^([^#{<\\]+)")
  local shard = ""
  local target_project = queued_urls
  if not target_project[shard] then
    target_project[shard] = {}
  end
  if not target_project[shard][url] then
    if find_path_loop(url, 3) then
      return false
    end
--print("queuing",original, url)
    target_project[shard][url] = current_url
  end
end

remove_param = function(url, param_pattern)
  local newurl = url
  repeat
    url = newurl
    newurl = string.gsub(url, "([%?&;])" .. param_pattern .. "=[^%?&;]*[%?&;]?", "%1")
  until newurl == url
  return string.match(newurl, "^(.-)[%?&;]?$")
end

queue_new_urls = function(url)
  if not url then
    return nil
  end
  local newurl = string.gsub(url, "([%?&;])[aA][mM][pP];", "%1")
  if url == current_url then
    if newurl ~= url then
      queue_url(newurl)
    end
  end
  for _, param_pattern in pairs(remove_params) do
    newurl = remove_param(newurl, param_pattern)
  end
  if newurl ~= url then
    queue_url(newurl)
  end
  newurl = string.match(newurl, "^([^%?&]+)")
  if newurl ~= url then
    queue_url(newurl)
  end
  url = string.gsub(url, "&quot;", '"')
  url = string.gsub(url, "&amp;", "&")
  for newurl in string.gmatch(url, '([^"\\]+)') do
    if newurl ~= url then
      queue_url(newurl)
    end
  end
end

report_bad_url = function(url)
  if current_url ~= nil then
    bad_urls[current_url] = true
  else
    bad_urls[string.lower(url)] = true
  end
end

strip_url = function(url)
  url = string.match(url, "^https?://(.+)$")
  newurl = string.match(url, "^www%.(.+)$")
  if newurl then
    url = newurl
  end
  return url
end

wget.callbacks.download_child_p = function(urlpos, parent, depth, start_url_parsed, iri, verdict, reason)
  local url = urlpos["url"]["url"]
  local parenturl = parent["url"]
  local extract_page_requisites = false

  if string.match(url, "^https?://(.+)$") == string.match(parenturl, "^https?://(.+)$") then
    return false
  end

  local current_settings_all = current_settings and current_settings["all"]
  local current_settings_any_domain = current_settings and current_settings["any_domain"]
  local same_domain = string.match(parenturl, "^(https?://[^/]+)") == string.match(url, "^(https?://[^/]+)")

  if string.match(url, "^ftp://") then
    ftp_urls[""][url] = current_url
    return false
  end

--print(url)

  if find_path_loop(url, 3) then
    return false
  end

  queue_url(url)
  return false
end

wget.callbacks.get_urls = function(file, url, is_css, iri)
  local html = nil

  if url then
    downloaded[url] = true
  end

  local function check(url, headers)
    local url = string.match(url, "^([^#]+)")
    url = string.gsub(url, "&amp;", "&")
    queue_url(url)
  end

  local function checknewurl(newurl, headers)
    if string.match(newurl, "^#") then
      return nil
    end
    if string.match(newurl, "\\[uU]002[fF]") then
      return checknewurl(string.gsub(newurl, "\\[uU]002[fF]", "/"), headers)
    end
    if string.match(newurl, "^https?:////") then
      check(string.gsub(newurl, ":////", "://"), headers)
    elseif string.match(newurl, "^https?://") then
      check(newurl, headers)
    elseif string.match(newurl, "^https?:\\/\\?/") then
      check(string.gsub(newurl, "\\", ""), headers)
    elseif not url then
      return nil
    elseif string.match(newurl, "^\\/") then
      checknewurl(string.gsub(newurl, "\\", ""), headers)
    elseif string.match(newurl, "^//") then
      check(urlparse.absolute(url, newurl), headers)
    elseif string.match(newurl, "^/") then
      check(urlparse.absolute(url, newurl), headers)
    elseif string.match(newurl, "^%.%./") then
      if string.match(url, "^https?://[^/]+/[^/]+/") then
        check(urlparse.absolute(url, newurl), headers)
      else
        checknewurl(string.match(newurl, "^%.%.(/.+)$"), headers)
      end
    elseif string.match(newurl, "^%./") then
      check(urlparse.absolute(url, newurl), headers)
    end
  end

  local function checknewshorturl(newurl, headers)
    if string.match(newurl, "^#") then
      return nil
    end
    if url and string.match(newurl, "^%?") then
      check(urlparse.absolute(url, newurl), headers)
    elseif url and not (string.match(newurl, "^https?:\\?/\\?//?/?")
      or string.match(newurl, "^[/\\]")
      or string.match(newurl, "^%./")
      or string.match(newurl, "^[jJ]ava[sS]cript:")
      or string.match(newurl, "^[mM]ail[tT]o:")
      or string.match(newurl, "^vine:")
      or string.match(newurl, "^android%-app:")
      or string.match(newurl, "^ios%-app:")
      or string.match(newurl, "^%${")) then
      check(urlparse.absolute(url, newurl), headers)
    else
      checknewurl(newurl, headers)
    end
  end

  if not url then
    html = read_file(file)
    if not url then
      html = string.gsub(html, "&#160;", " ")
      for pattern, replacement in pairs({
        ["&lt;"]="<",
        ["&gt;"]=">",
        ["&quot;"]='"',
        ["&apos;"]="'",
        [" +dot +"]="%.",
        [" +[%[%(]dot[%]%)] +"]="%.",
        ["˜"]="~"
      }) do
        html = string.gsub(html, pattern, replacement)
      end
      for _, pattern in pairs({
        "https?://www([^\032-\126]+)",
        "https?://[^/%.]+([^\032-\126]+)[^/%.]+/"
      }) do
        for s in string.gmatch(html, pattern) do
          --print("replacing", s)
          html = string.gsub(html, s, "%.")
        end
      end
      html = string.gsub(html, "&#(%d+);",
        function(n)
          return string.char(n)
        end
      )
      html = string.gsub(html, "&#x(%d+);",
        function(n)
          return string.char(tonumber(n, 16))
        end
      )
      local temp = html
      for _, remove in pairs({"", "<br/>", "</?p[^>]*>"}) do
        if remove ~= "" then
          temp = string.gsub(temp, remove, "\0")
        end
        temp2 = string.gsub(temp, "%s*\n%s*", "\n")
        temp2 = string.gsub(temp2, "([^>\"'\\`}%)%]%.,])\n%s*", "%1\0")
        for _, newline_white in pairs({" ", ""}) do
          temp3 = string.gsub(temp2, "\n", newline_white)
          local url_patterns = {
            "([hH][tT][tT][pP][sS]?://[^%s<>#\"'\\`{}%)%]]+)",
            '"([hH][tT][tT][pP][sS]?://[^"]+)',
            "'([hH][tT][tT][pP][sS]?://[^']+)",
            ">[%s%z]*([hH][tT][tT][pP][sS]?://[^<%s]+)"
          }
          if newline_white == " " then
            table.insert(url_patterns, "([a-zA-Z0-9%-%.%z]+%.[a-zA-Z0-9%-%.%z]+)")
            table.insert(url_patterns, "([a-zA-Z0-9%-%.%z]+%.[a-zA-Z0-9%-%.%z]+/[^%s<>#\"'\\`{}%)%]]+)")
            table.insert(url_patterns, "([a-zA-Z0-9%-%.%z]+%.[a-zA-Z0-9%-%.%z:]+)")
            table.insert(url_patterns, "([a-zA-Z0-9%-%.%z]+%.[a-zA-Z0-9%-%.%z:]+/[^%s<>#\"'\\`{}%)%]]+)")
          end
          for _, pattern in pairs(url_patterns) do
            for raw_newurl in string.gmatch(temp3, pattern) do
              local candidate_urls = {}
              local i = 0
              for s in string.gmatch(raw_newurl, "([^%z]+)") do
                local current_candidate = s
                local j = 0
                for t in string.gmatch(raw_newurl, "([^%z]+)") do
                  if j > i then
                    current_candidate = current_candidate .. t
                  end
                  candidate_urls[current_candidate] = true
                  j = j + 1
                end
                i = i + 1
              end
              for newurl, _ in pairs(candidate_urls) do
                while string.match(newurl, ".[%.&,!;]$") do
                  newurl = string.match(newurl, "^(.+).$")
                end
                if string.match(newurl, "^[hH][tT][tT][pP][sS]?://") then
                  local a, b = string.match(newurl, "^([hH][tT][tT][pP][sS]?://[^/]*)(.-)$")
                  newurl = string.lower(a) .. b
                  check(newurl)
                  check(html_entities.decode(newurl))
                elseif string.match(newurl, "^[a-zA-Z0-9]") then
                  if not string.find(newurl, "/") then
                    newurl = newurl .. "/"
                  end
                  local a, b = string.match(newurl, "^([^/]+)(/.*)$")
                  newurl = string.lower(a) .. b
                  local tld = string.match(newurl, "^[^/]+%.([a-z]+)[:/]")
                  if not tld then
                    tld = string.match(newurl, "^[^/]+%.(xn%-%-[a-z0-9]+)[:/]")
                  end
                  --print(newurl, tld, tlds[tld])
                  if tld and tlds[tld] then
                    check("http://" .. newurl)
                    check("https://" .. newurl)
                  end
                end
              end
            end
          end
        end
      end
    end
    for newurl in string.gmatch(html, "[^%-][hH][rR][eE][fF]='([^']+)'") do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(html, '[^%-][hH][rR][eE][fF]="([^"]+)"') do
      checknewshorturl(newurl)
    end
    for newurl in string.gmatch(string.gsub(html, "&[qQ][uU][oO][tT];", '"'), '"(https?://[^"]+)') do
      checknewurl(newurl)
    end
    for newurl in string.gmatch(string.gsub(html, "&#039;", "'"), "'(https?://[^']+)") do
      checknewurl(newurl)
    end
    if url then
      for newurl in string.gmatch(html, ">%s*([^<%s]+)") do
        checknewurl(newurl)
      end
    end
    --[[for newurl in string.gmatch(html, "%(([^%)]+)%)") do
      checknewurl(newurl)
    end]]
  end
  if url then
    --[[for _, extension in {
      "docx",
      "epub",
      "odt",
      "rtf"
    } do
      if string.match(string.lower(url, "[^a-z0-9]" .. extension .. "$")) then
        io.stdout:write("Converting to PDF.\n")
        io.stdout:flush()
        local copied_to = file .. "." .. extension
        os.execute("cp " .. file .. " " .. copied_to)
        local temp_file = copied_to .. ".pdf"
        local check_file = io.open(temp_file)
        if check_file then
          check_file:close()
          os.remove(temp_file)
        end
        os.execute("pandoc " .. copied_to .. " -o " .. temp_file .. " --pdf-engine pdfroff")
        os.remove(copied_to)
        check_file = io.open(temp_file)
        if check_file then
          check_file:close()
          wget.callbacks.get_urls(temp_file, url .. ".pdf", nil, nil)
          os.remove(temp_file)
        end
      end
    end]]
    local function extract_from_pdf(filepath)
      local temp_file = filepath .. "-html.html"
      local check_file = io.open(temp_file)
      if check_file then
        check_file:close()
        os.remove(temp_file)
      end
      os.execute("pdftohtml -nodrm -hidden -i -s -q " .. filepath)
      check_file = io.open(temp_file)
      if check_file then
        check_file:close()
        local temp_length = table_length(queued_urls[""])
        wget.callbacks.get_urls(temp_file, nil, nil, nil)
        io.stdout:write("Found " .. tostring(table_length(queued_urls[""])-temp_length) .. " URLs.\n")
        io.stdout:flush()
        os.remove(temp_file)
        return true
      end
      return false
    end
    if string.match(url, "^https?://[^/]+/.*[^a-z0-9A-Z][pP][dD][fF]$")
      or string.match(url, "^https?://[^/]+/.*[^a-z0-9A-Z][pP][dD][fF][^a-z0-9A-Z]")
      or string.match(read_file(file, 4), "%%[pP][dD][fF]") then
      io.stdout:write("Extracting links from PDF.\n")
      io.stdout:flush()
      if not extract_from_pdf(file) then
        io.stdout:write("Could not process PDF, attempting to repair.\n")
        io.stdout:flush()
        local repaired_file = file .. ".repaired"
        local returned = os.execute("ghostscript -o " .. repaired_file .. " -dQUIET -sDEVICE=pdfwrite -dPDFSETTINGS=/default " .. file .. " >/dev/null 2>&1")
        if returned == 0 then
          io.stdout:write("Repaired PDF.\n")
          io.stdout:flush()
          if not extract_from_pdf(repaired_file) then
            io.stdout:write("Could not process repaired PDF.\n")
            io.stdout:flush()
          end
        else
          io.stdout:write("Could not repair PDF.\n")
          io.stdout:flush()
        end
        local check_file = io.open(repaired_file)
        if check_file then
          check_file:close()
          os.remove(repaired_file)
        end
      end
    end
    if status_code == 200 then
      if string.match(url, "^https?://[^/]+/robots%.txt$")
        or string.match(url, "^https?://[^/]+/security%.txt$")
        or string.match(url, "^https?://[^/]+/%.well%-known/security%.txt$") then
        html = read_file(file) .. "\n"
        if not string.match(html, "<[^>]+/>")
          and not string.match(html, "</") then
          for line in string.gmatch(html, "(.-)\n") do
            local name, path = string.match(line, "([^:]+):%s*(.-)%s*$")
            if name and path and name ~= "http" and name ~= "https" then
              -- the path should normally be absolute already
              local newurl = urlparse.absolute(url, path)
              if string.lower(name) == "sitemap" then
                queue_url(newurl)
              elseif string.lower(name) ~= "user-agent"
                and not string.match(path, "%*")
                and not string.match(path, "%$") then
                queue_url(newurl)
              end
            end
          end
        end
      elseif string.match(url, "^https?://[^/]+/ads%.txt$")
        or string.match(url, "^https?://[^/]+/app%-ads%.txt$") then
        html = read_file(file) .. "\n"
        if not string.match(html, "<[^>]+/>")
          and not string.match(html, "</") then
          for line in string.gmatch(html, "(.-)\n") do
            if not string.match(line, "^#") then
              local site = string.match(line, "^([^,%s]+),")
              if site then
                if string.match(site, "^https?://") then
                  queue_url(site)
                else
                  queue_url("http://" .. site .. "/")
                  queue_url("https://" .. site .. "/")
                end
              end
            end
          end
        end
      elseif string.match(url, "^https?://[^/]+/%.well%-known/trust%.txt$") then
        html = read_file(file) .. "\n"
        if not string.match(html, "<[^>]+/>")
          and not string.match(html, "</") then
          for line in string.gmatch(html, "(.-)\n") do
            if not string.match(line, "^#") then
              local a, b = string.match(line, "^([^=]+)=%s*(https?://.-)%s*$")
              if b then
                queue_url(b)
              end
            end
          end
        end
      elseif string.match(url, "^https?://[^/]+/%.well%-known/nodeinfo$")
        or string.match(url, "^https?://[^/]+/%.well%-known/openid%-configuration$")
        or string.match(url, "^https?://[^/]+/%.well%-known/ai%-plugin%.json$") then
        html = read_file(file)
        html = string.gsub(html, "\\", "")
        if string.match(html, "^%s*{") then
          for s in string.gmatch(html, '([^"]+)') do
            if string.match(s, "^https?://") then
              queue_url(s)
            end
          end
        end
      end
    end
    if string.match(url, "sitemap.*%.gz$")
      or string.match(url, "%.xml%.gz") then
      local temp_file = file .. ".uncompressed"
      io.stdout:write("Attempting to decompress sitemap to " .. temp_file .. ".\n")
      io.stdout:flush()
      os.execute("gzip -kdc " .. file .. " > " .. temp_file)
      local check_file = io.open(temp_file)
      if check_file then
        io.stdout:write("Extracting sitemaps from decompressed sitemap.\n")
        io.stdout:flush()
        check_file:close()
        wget.callbacks.get_urls(temp_file, string.match(url, "^(.-)%.gz$"), nil, nil)
      end
    end
    if string.match(url, "^https?://[^/]+/.*%.[xX][mM][lL]")
      and string.match(string.lower(read_file(file, 200)), "sitemap") then
      html = read_file(file)
      for url in string.gmatch(html, "<[^>]+>%s*(https?://[^%s<]+)%s*<") do
        queue_url(url)
      end
      for sitemap in string.gmatch(html, "<sitemap>(.-)</sitemap>") do
        local newurl = string.match(sitemap, "<loc>%s*([^%s<]+)%s*</loc>")
        newurl = html_entities.decode(newurl)
        if newurl then
          -- should already be absolute
          newurl = urlparse.absolute(url, newurl)
          queue_url(newurl)
        end
      end
    end
  end
end

set_current_url = function(url)
  candidate_current = normalize_url(url)
  if candidate_current ~= current_url and urls[candidate_current] then
    current_url = candidate_current
  end
end

wget.callbacks.write_to_warc = function(url, http_stat)
  current_file = http_stat["local_file"]
  current_file_url = url["url"]
  current_file_html = nil
  set_current_url(url["url"])
  if current_settings and not current_settings["random"] then
    queue_url(url["url"])
    return false
  end
  if bad_code(http_stat["statcode"]) then
    return false
  end
  return true
end

wget.callbacks.httploop_result = function(url, err, http_stat)
  status_code = http_stat["statcode"]

  set_current_url(url["url"])

  local err_string = ""
  --[[if err ~= "RETRFINISHED" then
    err_string = err_string .. " (" .. err .. ")"
  end
  if http_stat["rderrmsg"] then
    err_string = err_string .. " (" .. http_stat["rderrmsg"] .. ")"
  end]]

  url_count = url_count + 1
  io.stdout:write(url_count .. "=" .. status_code .. err_string .. " " .. url["url"] .. "  \n")
  io.stdout:flush()

  if http_stat["res"] < 0 then
    report_bad_url(url["url"])
    return wget.actions.EXIT
  end

  if killgrab then
    return wget.actions.ABORT
  end

  local url_path = string.match(url["url"], "^https?://[^/]+(/[a-zA-Z0-9_%-%./]*)[^a-zA-Z0-9_%-%./]")
  if url_path
    and url_path ~= "/"
    and url_path ~= "/sitemap.xml"
    and paths[url_path] then
    return wget.actions.EXIT
  end

  if status_code < 400 then
    local base_url = string.match(url["url"], "^(https://[^/]+)")
    if base_url then
      if string.match(url["url"], "^https?://[^/]+/.") then
        queue_url(base_url .. "/")
      elseif string.match(url["url"], "^https?://[^/]+/$") then
        for path, _ in pairs(paths) do
          queue_url(base_url .. path)
        end
      end
    end
  end

  if redirect_domains["done"] then
    redirect_domains = {}
    redirect_urls = {}
    visited_urls = {}
    item_first_url = nil
  end
  redirect_domains[string.match(url["url"], "^https?://([^/]+)")] = true
  if not item_first_url then
    item_first_url = url["url"]
  end

  visited_urls[url["url"]] = true

  if exit_url then
    exit_url = false
    return wget.actions.EXIT
  end

  if status_code >= 300 and status_code <= 399 then
    local newloc = urlparse.absolute(url["url"], http_stat["newloc"])
    redirect_urls[url["url"]] = true
    --[[if strip_url(url["url"]) == strip_url(newloc) then
      queued_urls[""][newloc] = true
      return wget.actions.EXIT
    end]]
    if status_code == 301
      and string.match(newloc, "^https?://[^/]+/?$") then
      local url_path = string.match(url["url"], "^https?://[^/]+(/+)")
      if url_path and paths[url_path] then
        return wget.actions.EXIT
      end
    end
    local matching_domain = (
      string.match(newloc, "^https?://www%.(.+)")
      or string.match(newloc, "^https?://(.+)")
    ) == (
      string.match(url["url"], "^https?://www%.(.+)")
      or string.match(url["url"], "^https?://(.+)")
    )
    if downloaded[newloc]
      or string.match(newloc, "^magnet:") then
      return wget.actions.EXIT
    end
    local should_continue = false
    if not should_continue
      and (
        matching_domain
        or status_code == 301
        or status_code == 303
        or status_code == 308
      ) then
      queue_url(newloc)
      return wget.actions.EXIT
    end
  else
    redirect_domains["done"] = true
  end

  if downloaded[url["url"]] then
    report_bad_url(url["url"])
    return wget.actions.EXIT
  end

  if bad_code(status_code) then
    io.stdout:write("Server returned " .. http_stat.statcode .. " (" .. err .. ").\n")
    io.stdout:flush()
    report_bad_url(url["url"])
    return wget.actions.EXIT
  end

  if status_code >= 200 and status_code <= 399 then
    downloaded[url["url"]] = true
  end

  if status_code >= 200 and status_code < 300 then
    queue_new_urls(url["url"])
  end

  local sleep_time = 0

  if sleep_time > 0.001 then
    os.execute("sleep " .. sleep_time)
  end

  return wget.actions.NOTHING
end

wget.callbacks.finish = function(start_time, end_time, wall_time, numurls, total_downloaded_bytes, total_download_time)
  local function submit_backfeed(newurls, key, shard)
    local tries = 0
    local maxtries = 10
    local parameters = ""
    if shard ~= "" then
      parameters = "?shard=" .. shard
    end
    while tries < maxtries do
      if killgrab then
        return false
      end
      local body, code, headers, status = http.request(
        "https://legacy-api.arpa.li/backfeed/legacy/" .. key .. parameters,
        newurls .. "\0"
      )
      print(body)
      if code == 200 and body ~= nil and cjson.decode(body)["status_code"] == 200 then
        io.stdout:write("Submitted discovered URLs.\n")
        io.stdout:flush()
        break
      end
      io.stdout:write("Failed to submit discovered URLs." .. tostring(code) .. tostring(body) .. "\n")
      io.stdout:flush()
      os.execute("sleep " .. math.floor(math.pow(2, tries)))
      tries = tries + 1
    end
    if tries == maxtries then
      kill_grab()
    end
  end

  for key, items_data in pairs({
    ["usgovernment-inbox-c7hgbf30vmn7gkv6"] = queued_urls,
    ["ftp-urls-en2fk0pjyxljsf9"] = ftp_urls,
  }) do
    local project_name = string.match(key, "^(.+)%-")
    for shard, url_data in pairs(items_data) do
      local count = 0
      local newurls = nil
      print("Queuing to project " .. project_name .. " on shard " .. shard)
      local sorted_data = {}
      for url, parent_url in pairs(url_data) do
        if not sorted_data[parent_url] then
          sorted_data[parent_url] = {}
        end
        sorted_data[parent_url][url] = true
      end
      for parent_url, urls_list in pairs(sorted_data) do
        if true then --not skip_parent_urls[parent_url] then
          io.stdout:write("Queuing for parent URL " .. tostring(parent_url) .. ".\n")
          io.stdout:flush()
          for url, _ in pairs(urls_list) do
            local filtered = false
            local actual_url = url
            if not filtered then
              io.stdout:write("Queuing URL " .. url .. ".\n")
              io.stdout:flush()
              if newurls == nil then
                newurls = url
              else
                newurls = newurls .. "\0" .. url
              end
              count = count + 1
              if count == 400 then
                submit_backfeed(newurls, key, shard)
                newurls = nil
                count = 0
              end
            end
          end
        end
      end
      if newurls ~= nil then
        submit_backfeed(newurls, key, shard)
      end
    end
  end

  local file = io.open(item_dir .. "/" .. warc_file_base .. "_bad-urls.txt", "w")
  for url, _ in pairs(bad_urls) do
    file:write(urlparse.escape(url) .. "\n")
  end
  file:close()
end

wget.callbacks.before_exit = function(exit_status, exit_status_string)
  if killgrab then
    return wget.exits.IO_FAIL
  end
  if abortgrab then
    return wget.exits.IO_FAIL
  end
  return exit_status
end

