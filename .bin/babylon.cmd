@IF EXIST "%~dp0\node.exe" (
  "%~dp0\node.exe"  "%~dp0\..\babel-eslint\node_modules\babylon\bin\babylon.js" %*
) ELSE (
  @SETLOCAL
  @SET PATHEXT=%PATHEXT:;.JS;=;%
  node  "%~dp0\..\babel-eslint\node_modules\babylon\bin\babylon.js" %*
)