function livenumber = findlive(matrix,xt,yt,sample)
%FINDLIVE 此处显示有关此函数的摘要
% 找color色棋子的活num数量
    [leng,width] = size(matrix);
    livenumber = 0;
    samplen = length(sample);
    for y = 1 : width-samplen+1
        if matrix(xt,y:y+samplen-1)==sample
                livenumber = livenumber + 1;
        end
    end
    for x =1 : leng - samplen + 1
          if matrix(x:x+samplen-1,yt)==transpose(sample)
                livenumber = livenumber + 1;
         end
    end
    for x = 1 : leng-samplen+1
      y = x + yt-xt;
      if y + samplen -1 <= width  && y > 0
            flag = 1;
            for i = 0 : samplen - 1
                if matrix(x+i,y+i)~= sample(i+1)
                    flag = 0;
                end
            end
            if flag == 1  
                livenumber = livenumber + 1;
            end
      end
    end
    for x = samplen : leng
        y = xt+yt-x;
        if y > 0 && y+samplen-1 <= width
            flag = 1;
            for i = 0 : samplen - 1
                if matrix(x-i,y+i)~=sample (i+1)
                    flag = 0;
                end
            end
            if flag == 1  
                livenumber = livenumber + 1;
            end
        end
    end
end

