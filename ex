ls -ldO .metals    # shows file flags (e.g. uchg, schg)
ls -le  .metals    # shows any ACL entries
xattr -lr .metals  # shows extended attributes
chflags -R nouchg,noschg .metals
chmod -RN .metals
xattr -rc .metals
rm -rf .metals
