@IF EXIST "%~dp0\node.exe" (
  "%~dp0\node.exe"  "%~dp0\..\@babel\helper-create-regexp-features-plugin\node_modules\regjsparser\bin\parser" %*
) ELSE (
  @SETLOCAL
  @SET PATHEXT=%PATHEXT:;.JS;=;%
  node  "%~dp0\..\@babel\helper-create-regexp-features-plugin\node_modules\regjsparser\bin\parser" %*
)